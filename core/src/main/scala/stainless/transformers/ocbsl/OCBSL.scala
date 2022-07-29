package stainless
package transformers
package ocbsl

import inox.solvers

trait OCBSL extends Definitions { ocbsl =>
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable // A bit ironic that we import mutable stuff right after "Purity"...

  // Not for sparing allocations, but for sparing key strokes :p
  val BoolTy: Type = BooleanType()


  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def isPrefixOf[T](lhs: Seq[T], rhs: Seq[T]): Boolean =
    lhs.size <= rhs.size && lhs.zip(rhs).forall { case (l, r) => l == r }

  def findMap[A, B](as: Seq[A])(f: A => Option[B]): Option[B] =
    if (as.isEmpty) None
    else f(as.head).orElse(findMap(as.tail)(f))

  case class OEnv(varSubst: Map[VarId, Code],
                  inLambda: Boolean,
                  forceBinding: Boolean) {
    assert(varSubst.values.forall(c => code2sig(c).label.isLitOrVar))
    assert(varSubst.values.flatMap { c =>
      code2sig(c).label match {
        case Label.Var(v) => Some(v)
        case _ => None
      }
    }.toSet.intersect(varSubst.keySet).isEmpty) // pas d'alias d'alias etc.

    def addVarSubst(from: VarId, to: VarId): OEnv = {
      assert(from != to)
      copy(varSubst = varSubst + (from -> codeOfVarId(to)))
    }

    def addLitSubst[T](v: VarId, lit: Literal[T]): OEnv = copy(varSubst = varSubst + (v -> codeOfLit(lit)))
  }

  object OEnv {
    def empty: OEnv = OEnv(Map.empty, false, false)
  }

  case class LetBind(v: Option[VarId], tpe: Type) {
    def getOrFresh(name: String = "bdg"): VarId = v.getOrElse(freshVarId(name, tpe))
  }
  object LetBind {
    def of(v: VarId): LetBind = LetBind(Some(v), varTpe(v))
    def empty(tpe: Type): LetBind = LetBind(None, tpe)
  }

  case class InLambda(v: Boolean) {
    def ||(other: Boolean): InLambda = InLambda(v || other)
    def ||(other: InLambda): InLambda = InLambda(v || other.v)
  }

  enum Ctx {
    case Id
    case BoundDef(vId: VarId, terminal: Code, composition: Occurrences)
//    case UnboundDef(terminal: Code, composition: Occurrences)
    case AssumeLike(lab: Label.AssumeLike, predTerminal: Code)
    case Assumed(cond: Code) // TODO: Dire que c'est p.ex. apres if (cond), où le assume(cond) ds la branche n'est pas nécessaire (car impliqué)

    lazy val hc: Int = this match {
      case Ctx.Id => 31
      case Ctx.BoundDef(v, t, c) => java.util.Objects.hash(v, t, c)
      case Ctx.AssumeLike(l, p) => java.util.Objects.hash(l, p)
      case Ctx.Assumed(c) => java.util.Objects.hash(c)
    }
    override def hashCode(): Int = hc

    def isBoundDef(c: Code): Boolean = this match {
      case Ctx.BoundDef(_, c2, _) => c == c2
      case _ => false
    }

    def bindingOf(c: Code): Option[BoundDef] = this match {
      case b@Ctx.BoundDef(_, c2, _) if c == c2 => Some(b)
      case _ => None
    }

    def varBindingOf(c: Code): Option[VarId] = bindingOf(c).map(_.vId)

    def boundTo(v: VarId): Option[Code] = this match {
      case Ctx.BoundDef(v2, c, _) if v == v2 => Some(c)
      case _ => None
    }
  }

  case class Ctxs(ctxs: Seq[Ctx]) {
    assert(
      ctxs.forall {
        case Ctx.BoundDef(_, terminal, _) => !code2sig(terminal).label.isLitOrVar
        case _ => true
      }, "Binding de var ou lit")
    assert(
      ctxs.collect {
        case bd@Ctx.BoundDef(_, _, _) => bd
      }.groupBy(_.terminal).forall(_._2.size == 1),
      "Double binding")

    lazy val hc: Int = java.util.Objects.hash(ctxs)
    override def hashCode(): Int = hc

    lazy val allConds: Seq[Code] = ctxs.foldLeft(Seq.empty[Code]) {
      case (acc, Ctx.AssumeLike(lab, c)) if !lab.isDecreases => acc :+ c
      case (acc, Ctx.Assumed(c)) => acc :+ c
      case (acc, _) => acc
    }
    lazy val allCondsSet: Set[Code] = allConds.toSet

    lazy val bindings: Seq[(VarId, Code)] = ctxs.collect {
      case Ctx.BoundDef(v, c, _) => (v, c)
    }

    def pop: Option[(Ctxs, Ctx)] = {
      if (ctxs.isEmpty) None
      else Some((Ctxs(ctxs.init), ctxs.last))
    }
    def popOrId: (Ctxs, Ctx) = pop.getOrElse((Ctxs(Seq.empty), Ctx.Id))

    def withRemovedBinding(v: VarId): Ctxs = {
      Ctxs(ctxs.filterNot {
        case Ctx.BoundDef(`v`, _, _) => true
        case _ => false
      })
    }

    // En gros: On plug jusqu'à ce que l'on atteigne inCtxs
    def plugged(inCtxs: Ctxs, u: Occurrences, c: Code)(using env: OEnv): (Occurrences, Code) = {
      assert(inCtxs.isPrefixOf(this))

      def plugCtx(curr: Ctxs, prev: Ctxs, toPlug: Ctx, u: Occurrences, c: Code): (Occurrences, Code) = {
        assert(curr.ctxs == prev.ctxs :+ toPlug)
        val uuu = occurrencesOf(c)(using env, curr)
//        if (u != uuu) {
//          println("!!! Pas d'égalité")
//        }

        val (u2, c2) = toPlug match {
          case Ctx.Id | Ctx.Assumed(_) => (u, c)

          case Ctx.BoundDef(vId, terminal, composition) =>
            assert(!code2sig(terminal).label.isLitOrVar)
            assert(composition(terminal).isZero)
            val expl = asExplicitSig(c)
            val isLam = isLambda(terminal)
            // Rappel: pr les lambdas, le code utilisé est celui de vId, pas de e.terminal!
            val defnCode = if (!isLam) terminal else codeOfVarId(vId)
            assert(composition(defnCode).isZero)
            val definitionOccurrence = u(defnCode)
            val bdgCase = needsBinding(vId, terminal, composition, definitionOccurrence)(using env, prev)

            val ccc = codeOfVarId(vId)
            val nme = varId2Var(vId).toString

            if (bdgCase == BindingCase.MustBind || isLam) {
              val cLet = codeOfSig(mkLet(vId, terminal, c), codeTpe(c))
              // TODO: pr le setTo: y-a-t-il tjrs un sens à cela? parce que de toute façon, on est sensé bind "tout en haut" non?
              // TODO: inCtx: avec ou sans le binding?
              val u2 = composition ++ u.setTo(defnCode, Occurrence.Once(prev, env.inLambda)) // TODO: Hmm est-ce "vrai"?
              (u2, cLet)
            } else if (bdgCase == BindingCase.Inlinable && isLam) {
              println("inlining "+vId + "   " + varId2Var(vId))
              val res = inlineLetBoundLambda(vId, terminal, c)(using env, prev)
              assert(prev.isPrefixOf(res.ctxs))
              //          val plugged = res.ctxs.plugged(, res.terminal)
              val (u2, c2) = res.selfPlugged(prev) // .ctxs.plugged(, res.terminal)
              //          println("FINISHED INLINING")
//              val u3 = Occurrences(u2.c2u.map {
//                case (c, Occurrence.Once(inCtxs, inLambda)) =>
//                  c -> Occurrence.Once(inCtxs.withRemovedBinding(vId), inLambda)
//                case (c, occ) => c -> occ
//              })
              (u2, c2)
            } else {
              assert(!definitionOccurrence.isMany)
              val u2 = {
                if (definitionOccurrence.isZero) u
                else u ++ composition
              }
              // TODO: Remettre
//              val u3 = Occurrences(u2.c2u.map {
//                case (c, Occurrence.Once(inCtxs, inLambda)) =>
//                  c -> Occurrence.Once(inCtxs.withRemovedBinding(vId), inLambda)
//                case (c, occ) => c -> occ
//              })
              (u2, c)
            }

          case Ctx.AssumeLike(lab, predTerminal) =>
            assert(code2sig(predTerminal).label.isLitOrVar || prev.isBoundDef(predTerminal))
            val c2 = codeOfSig(mkAssumeLike(lab, predTerminal, c), codeTpe(c))
            (u ++ Occurrences.of(predTerminal)(using env, prev), c2)
        }
//        val u3 = Occurrences(u2.c2u.map {
//          case (c, Occurrence.Once(inCtxs, inLambda)) =>
//            // assert(inCtxs == curr || inCtxs == prev)
//            c -> Occurrence.Once(prev, inLambda) // TODO: !!!! pas si apparait "plus loin" !!!
//          case (c, occ) => c -> occ
//        })
        (u2, c2)
      }

      def rec(curr: Ctxs, u: Occurrences, c: Code): (Occurrences, Code) = {
        assert(inCtxs.isPrefixOf(curr))
        assert(curr.isPrefixOf(this))
        if (curr.ctxs.size == inCtxs.ctxs.size) (u, c)
        else {
          assert(curr.ctxs.nonEmpty)
          val (prev, toPlug) = curr.popOrId
          val (u2, c2) = plugCtx(curr, prev, toPlug, u, c)
          rec(prev, u2, c2)
        }
      }

      rec(this, u, c)
    }

    def isBoundDef(c: Code): Boolean = ctxs.exists(_.isBoundDef(c))

    def bindingOf(c: Code): Option[Ctx.BoundDef] = findMap(ctxs)(_.bindingOf(c))

    def varBindingOf(c: Code): Option[VarId] = findMap(ctxs)(_.varBindingOf(c))

    def boundTo(v: VarId): Option[Code] = findMap(ctxs)(_.boundTo(v))

    def isPrefixOf(that: Ctxs): Boolean = ocbsl.isPrefixOf(ctxs, that.ctxs)

    def addBoundDef(v: VarId, df: Code, composition: Occurrences): Ctxs = {
      assert(composition(df).isZero)

      if (isBoundDef(df)) {
        assert(ctxs.exists {
          case Ctx.BoundDef(_, otherTerm, otherComp) =>
            // Pour comp: slmt les codes car les counts peuvent être différents
            otherTerm == df && otherComp.c2u.keySet == composition.c2u.keySet
          case _ => false
        })
        this
      } else {
        Ctxs(ctxs :+ Ctx.BoundDef(v, df, composition))
      }
    }

    def withCond(cond: Code): Ctxs = {
      // assert(code2sig(cond).label.isLitOrVar || isBoundDef(cond)) // TODO: Non, c'est que pr les Or, if branch etc.
      if (cond == trueCode || allCondsSet.contains(cond)) this
      else Ctxs(ctxs :+ Ctx.Assumed(cond))
    }

    def withConds(conds: Seq[Code]): Ctxs = {
      // assert(conds.forall(c => code2sig(c).label.isLitOrVar || isBoundDef(c))) // TODO: Non, c'est que pr les Or, if branch etc.
      val toAdd = conds.distinct.filterNot(allCondsSet)
      if (toAdd.isEmpty) this
      else Ctxs(ctxs ++ toAdd.map(Ctx.Assumed.apply))
    }

    def withAssumeLike(kind: Label.AssumeLike, pred: Code, predComp: Occurrences): Ctxs = {
      assert(code2sig(pred).label.isLitOrVar || isBoundDef(pred))
      if (pred == trueCode || (!kind.isDecreases && allCondsSet.contains(pred))) this
      else Ctxs(ctxs :+ Ctx.AssumeLike(kind, pred))
    }
  }

  object Ctxs {
    def apply(ctxs: Seq[Ctx]): Ctxs = new Ctxs(ctxs.filter(_ != Ctx.Id))

    def apply(ctx1: Ctx, ctxs: Ctx*): Ctxs = new Ctxs((ctx1 +: ctxs).filter(_ != Ctx.Id))

    def empty: Ctxs = new Ctxs(Seq.empty)
  }

  enum Occurrence {
    case Zero
    case Once(inCtxs: Ctxs, inLambda: Boolean)
    case Many

    def ++(that: Occurrence): Occurrence = (this, that) match {
      case (Zero, _) => that
      case (_, Zero) => this
      case _ => Many
    }

    def isZero: Boolean = this match {
      case Zero => true
      case _ => false
    }
    def isOnce: Boolean = this match {
      case Once(_, _) => true
      case _ => false
    }
    def isMany: Boolean = this match {
      case Many => true
      case _ => false
    }

    def nonZero: Boolean = !isZero

    override def toString: String = this match {
      case Zero => "Zero"
      case Once(_, _) => "Once"
      case Many => "Many"
    }
  }

  case class Occurrences(c2u: Map[Code, Occurrence]) {
    def hasLambda: Boolean = c2u.keys.exists(c => code2sig(c).label.isLambda)

    def apply(c: Code): Occurrence = c2u.getOrElse(c, Occurrence.Zero)

    def ++(that: Occurrences): Occurrences = Occurrences((c2u.keySet ++ that.c2u.keySet)
      .map(c => c -> (this(c) ++ that(c))).toMap)

    def setTo(c: Code, o: Occurrence): Occurrences = Occurrences(c2u + (c -> o))

    // TODO: What is this name!!!!
    def manyied: Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Zero) => (c, Occurrence.Zero) // TODO: Should we just filter these out?
      case (c, _) => c -> Occurrence.Many
    })
  }

  object Occurrences {
    def empty: Occurrences = Occurrences(Map.empty)

    def of(c: Code)(using env: OEnv, ctxs: Ctxs): Occurrences = {
      if (code2sig(c).label.isLiteral) Occurrences.empty
      else Occurrences(Map(c -> Occurrence.Once(ctxs, env.inLambda)))
    }
  }

  private val pluggedMap = mutable.Map.empty[(CodeRes, Ctxs, OEnv), (Occurrences, Code)]
  private val unplugMap = mutable.Map.empty[(Code, OEnv), (CodeRes, Occurrences)]

  def unplugged(c: Code)(using env: OEnv): Option[(CodeRes, Occurrences)] = unplugMap.get((c, env))

  case class CodeRes(terminal: Code,
                     terminalComposition: Occurrences,
                     ctxs: Ctxs) {
    assert(CodeRes.isTerminal(terminal), s"Gag: $terminal n'est pas un terminal (est un ${code2sig(terminal)})")
    assert(!isLambda(terminal))
    // assert(terminalComposition(terminal).isZero, s"Gag: $terminal (${code2sig(terminal)}) apparait dans $terminalComposition !!!") // TODO: Bah non...

    lazy val hc: Int = java.util.Objects.hash(terminal, terminalComposition, ctxs)
    override def hashCode(): Int = hc

    def selfPlugged(inCtxs: Ctxs)(using env: OEnv): (Occurrences, Code) = {
      pluggedMap.getOrElseUpdate((this, inCtxs, env), {
        assert(inCtxs.isPrefixOf(ctxs))
        val u = Occurrences.of(terminal)(using env, ctxs)
//        val pluggedCtxs = Ctxs(ctxs.ctxs.drop(inCtxs.ctxs.size))
//        val (u2, c) = pluggedCtxs.plugged(u, terminal)
        val (u2, c) = ctxs.plugged(inCtxs, u, terminal)
        assert(codeTpe(terminal) == codeTpe(c), s"${codeTpe(terminal)} != ${codeTpe(c)}")
//        assert(unplugMap.get((c, env)).forall(_ == (this, u2))) // TODO
        unplugMap += (c, env) -> (this, u2)
        (u2, c)
      })
    }

    // Lorsque newTerminal est une var/lit ou déjà bound
    def derivedFromCtxs(newTerminal: Code)(using env: OEnv): CodeRes = {
      if (code2sig(newTerminal).label.isLitOrVar) derivedVarOrLit(newTerminal)
      else {
        ctxs.bindingOf(newTerminal) match {
          case Some(Ctx.BoundDef(_, _, comp)) => derived(newTerminal, comp)
          case None => sys.error(s"Trahison! Trahison! On nous avait promis que $newTerminal se trouverait dans $ctxs :(")
        }
      }
    }

    private def derivedVarOrLit(newTerminal: Code)(using env: OEnv): CodeRes = {
      code2sig(newTerminal).label match {
        case Label.Var(v) =>
          assert(!env.varSubst.contains(v)) // On suppose que c'est déjà substed
          copy(terminal = newTerminal, Occurrences.of(newTerminal)(using env, ctxs))
        case Label.Lit(_) => copy(terminal = newTerminal, Occurrences.empty)
        case sig => sys.error(s"On nous a menti :( $sig")
      }
    }

    // TODO: Remarque: on ne pop pas le ctx sur lequel le terminal actuel a été construit, car celui ci pourrait etre impure
    def derived(newTerminal: Code, newTerminalComposition: Occurrences)(using env: OEnv): CodeRes = {
      assert(CodeRes.isTerminal(newTerminal), s"Gag: le nouveau terminal $newTerminal n'est pas un terminal (est un ${code2sig(newTerminal)})")
      if (code2sig(newTerminal).label.isLitOrVar) {
        assert(newTerminalComposition == Occurrences.of(newTerminal)(using env, ctxs))
        derivedVarOrLit(newTerminal)
      } else {
        val bdg = freshVarId("derivedBdg", codeTpe(newTerminal))
        CodeRes(newTerminal, newTerminalComposition, ctxs.addBoundDef(bdg, newTerminal, newTerminalComposition))
      }

//      if (ctxs.isBoundDef(newTerminal)) {
//        CodeRes(newTerminal, newTerminalComposition, ctxs)
//      } else {
//        // TODO
////        assert(!env.isBound(newTerminal))
//        val (newCtx, newEnv) = newSig match {
//          case Signature(Label.Lambda(_) | Label.Choose(_) | Label.Forall(_) | Label.Ensuring, _) =>
//            // val (bodyUnpl, bodyUsgs) = unplugMap(body)  // TODO: bodyUsgs comprend body dans les usages. ok?
//            // combinedUnboundCtx(newTerminal)(Seq(ctx))(_ ++ newUsgs)
//            (Ctxs(Ctx.UnboundDef(newTerminal, newUsgs)), env)
//          case Signature(_, _) =>
//            // TODO: Pas si une variable/literal
//            // TODO: Ou bien?
//            if (newSig.label.isLitOrVar) {
//              (Ctxs.empty, env)
//            } else {
//              val bdg = freshVarId("bdg", codeTpe(newTerminal))
//              val newCtx = Ctx.BoundDef(bdg, newTerminal, newTermHasLambdaDef, newUsgs, env, canSubst = true)
//              (Ctxs(newCtx), env.withLetBound(bdg, newTerminal, canSubst = true))
//            }
//          // combinedBindingCtx(newTerminal, newTermHasLambdaDef)(Seq(ctx))(_ ++ newUsgs)
//        }
//        CodeRes(newTerminal, newTermHasLambdaDef, ctxs ++ newCtx, newUsgs, newEnv)
//      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???

  // TODO: On pourrait simplifier les trucs du genre !isInstanceOf[A] && isInstanceOf[B] en isInstanceOf[B] pour les patmat?

  // TODO (liste de rappel):
  //    - Pour le cache, il faudra qu'on serialize les mapping signature -> code
  //    Il faudra aussi que ce mapping soit le même pr ts les threads!!!
  //      -sig2code: on ajoute 1 indirection par ordinal de label pour diminuer les contention
  //      -code2sig: un simple atomicref d'array fera amplement l'affaire (faudra faire attention pr ne pas faire des allocs concurrentes...)

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

  private val sig2code = mutable.Map.empty[Signature, Code]
  private val code2sig = mutable.Map.empty[Code, Signature]
  private val sizeCache = mutable.Map.empty[Expr, Int]
  private val codeTpe = mutable.Map.empty[Code, Type]

  private var varIdCounter: Int = 0
  private val varId2Var = mutable.Map.empty[VarId, Variable]
  private val var2VarId = mutable.Map.empty[Variable, VarId]

  private val purityCache = mutable.Map.empty[Identifier, Boolean]
  private val codePurityCache = mutable.Map.empty[Code, Boolean]
  private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
  private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
  private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V
  private val visiting = mutable.Set.empty[Identifier]

  private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
  private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
  private val unitSig = Signature(Label.Lit(UnitLiteral()), Seq.empty)
  private val falseCode = codeOfSig(falseSig, BoolTy)
  private val trueCode = codeOfSig(trueSig, BoolTy)
  private val unitCode = codeOfSig(unitSig, UnitType())

//  // TODO: fusionner les deux fns?
//  def codeOfExpr(e: Expr)(using OEnv, InLambda): CodeRes = {
////    if (e.getType == BoolTy) simplifiedDisjunction(pDisj(e).toSet)
////    else {
////      val sig = sigOfExpr(e)
////      codeOfSig(sig, e.getType)
////    }
//    // TODO: fusionner les deux fns?
//    sigOfExpr(e)
//  }

  // TODO: !!!! Si un OEnv est ajouté, penser à regarder que toutes les refs soient correctes !!!!
  def negCodeOf(c: Code): Code = {
    assert(codeTpe(c) == BoolTy, s"Got ${codeTpe(c)}")
    code2sig(c) match {
      case Signature(Label.Not, Seq(cc)) => cc
      case Signature(Label.Lit(BooleanLiteral(b)), Seq()) => b2c(!b)
      case Signature(Label.LessThan, Seq(lhs, rhs)) => codeOfSig(mkGreaterEquals(lhs, rhs), BoolTy)
      case Signature(Label.GreaterEquals, Seq(lhs, rhs)) => codeOfSig(mkLessThan(lhs, rhs), BoolTy)
      case Signature(Label.GreaterThan, Seq(lhs, rhs)) => codeOfSig(mkLessEquals(lhs, rhs), BoolTy)
      case Signature(Label.LessEquals, Seq(lhs, rhs)) => codeOfSig(mkGreaterThan(lhs, rhs), BoolTy)
      case _ => codeOfSig(mkNot(c), BoolTy)
    }
  }

  // TODO: Pk ce truc est fait dans codeOf mais pas dans pDisj?
  // TODO: Et les assms???
  def simplifiedDisjunction(disj0: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, Ctxs): Code = {
    assert(disj0.forall(c => codeTpe(c) == BoolTy))
    val disj = unOrCodes(disj0)
    val disj1 = disj.filter(_ != falseCode).distinct
    if (disj1.isEmpty) falseCode
    else if (disj1.size == 1) disj1.head
    // TODO: mayDrop trop contraignant! On peut utiliser le short circuiting: si on a qqchose de true et que tout ce qu'on a parcouru est pure, on peut tout drop et retourner true
    else if (mayDrop && (disj1.contains(trueCode) || checkForContradiction(disj1))) trueCode
    else {
      val disj2 = if (mayReorder) disj1.sorted else disj1
      codeOfSig(mkOr(disj2), BoolTy)
    }
  }

  enum BindingCase {
    // In let v = e in body...
    case Elidable // ... the `e` (and the let) can be removed (that is, we can just return `body`, `e` is pure)
    case Inlinable // ... the `e` can be inlined or bound, but it definitely appears in `body` (may or may not be impure)
    case MustBind // ... the `e` must be bound (appears in `body` if pure, may not appear if impure)
  }

  def needsBinding(v: VarId, terminal: Code, terminalComposition: Occurrences, definitionOccurrence: Occurrence)(using env: OEnv, prefix: Ctxs): BindingCase = {
    assert(!prefix.isBoundDef(terminal))
    assert(prefix.boundTo(v).isEmpty)

    code2sig(terminal) match {
      case Signature(Label.Lit(_) | Label.Var(_), _) => BindingCase.Elidable
      case _ =>
        if (env.forceBinding) BindingCase.MustBind
        else {
//          val vvv = varId2Var(v)
//          val ccc = codeOfVarId(v)
//          if (vvv.toString.contains("prev$1$1") || vvv.toString.contains("lam$12") || vvv.toString.contains("proof$19") || vvv.toString.contains("x$114") || vvv.toString.contains("x$118")) {
//            println("AAAAA")
//          }
          lazy val isPure = codePurity(terminal).isPure
          definitionOccurrence match {
            case Occurrence.Many => BindingCase.MustBind
            case Occurrence.Zero =>
              // Si une expr impure n'apparait pas dans le body, on ne peut pas l'éliminer, il faut donc le bind
              if (!isPure) BindingCase.MustBind
              else BindingCase.Elidable
            case Occurrence.Once(inCtxs, inLambda) if isPure =>
              assert(prefix.isPrefixOf(inCtxs))
              assert(prefix.ctxs.size + 1 <= inCtxs.ctxs.size)
              assert(inCtxs.ctxs(prefix.ctxs.size) == Ctx.BoundDef(v, terminal, terminalComposition))
              if (inLambda && terminalComposition.hasLambda) BindingCase.MustBind
              else BindingCase.Inlinable
            case Occurrence.Once(inCtxs, inLambda) =>
              // TODO: Expliquer cette daube
              // inEnv représente l'env. actif lors de l'occurrence de `terminal` dans le trou que l'on s'apprête à compléter.
              // S'il est différent de l'env ou `terminal` est introduit, alors on a besoin de let-bind, car inline
              // une expr impure après un PC est incorrect.
              assert(prefix.isPrefixOf(inCtxs))
              // Dans inCtxs, on nécessairement le binding v -> terminal juste après prefix
              assert(prefix.ctxs.size + 1 <= inCtxs.ctxs.size)
              assert(inCtxs.ctxs(prefix.ctxs.size) == Ctx.BoundDef(v, terminal, terminalComposition))

              // TODO: inEnv.letDef.drop(env.letDef.size + 1)
              // Pour qu'on puisse inline cette expression impure...
              // 1. Pas dans une lambda
              // 2. Pas de nouvelles conditions (assumptions/PC)
              // 3. Tous les bindings supplémentaires (*après celui-ci*) sont pures
              // 2 et 3 sont gérés par isPureSuffix

              val isPureSuffix: Boolean = {
                def rec(extras: Seq[Ctx], running: Ctxs): Boolean = {
                  assert(extras.forall(ex => !running.ctxs.contains(ex)))
                  assert(running.isPrefixOf(inCtxs))
                  if (extras.isEmpty) true
                  else extras.head match {
                    case Ctx.Id => sys.error("Les Id devraient être filtré!!!")
                    case Ctx.Assumed(_) | Ctx.AssumeLike(_, _) => false // Condition supplémentaire; donc impure
                    case Ctx.BoundDef(bdg, defn, comp) =>
                      codePurity(defn)(using env, running).isPure &&
                        rec(extras.tail, running.addBoundDef(bdg, defn, comp))
                  }
                }
                val extras = inCtxs.ctxs.drop(prefix.ctxs.size + 1) // +1 car c'est après ce binding
                rec(extras, prefix.addBoundDef(v, terminal, terminalComposition))
              }

              if (!inLambda && isPureSuffix) BindingCase.Inlinable
              else BindingCase.MustBind
          }
        }
    }
  }

  def codeOfExprsBound(es: Seq[Expr], lb: LetBind)(cons: Seq[Code] => Signature)(using OEnv, Ctxs): CodeRes =
    codeOfExprsBound(es, lb)(cs => codeOfSig(cons(cs), lb.tpe))

  def codeOfExprsBound(e1: Expr, lb: LetBind)(cons: Code => Signature)(using OEnv, Ctxs): CodeRes =
    codeOfExprsBound(Seq(e1), lb) { case Seq(c1) => cons(c1) }

  def codeOfExprsBound(e1: Expr, e2: Expr, lb: LetBind)(cons: (Code, Code) => Signature)(using OEnv, Ctxs): CodeRes =
    codeOfExprsBound(Seq(e1, e2), lb) { case Seq(c1, c2) => cons(c1, c2) }

  def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, lb: LetBind)(cons: (Code, Code, Code) => Signature)(using OEnv, Ctxs): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), lb) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def codeOfExprsBound(es: Seq[Expr], lb: LetBind)(cons: Seq[Code] => Code)(using env: OEnv, ctxs: Ctxs, d: DummyImplicit): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    val (newCtxs, codeRess) = es.foldLeft((ctxs, Seq.empty[CodeRes])) {
      case ((ctxs, codeResAcc), e) =>
        // Remarque: on met un LetBind.empty car c'est pas ce résultat qu'on souhaite bind.
        val codeResE = codeOfExpr(e)(using env, ctxs)
        assert(ctxs.isPrefixOf(codeResE.ctxs))
        (codeResE.ctxs, codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess, lb)(cons)(using env, newCtxs)
  }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def combineCodeRes(codeRess: Seq[CodeRes], lb: LetBind)(cons: Seq[Code] => Code)(using env: OEnv, ctxs: Ctxs, d: DummyImplicit): CodeRes = {
    assert(codeRess.isEmpty || (ctxs eq codeRess.last.ctxs))
    assert(codeRess.forall(_.ctxs.isPrefixOf(ctxs)))
    assert(codeRess.size <= 1 || codeRess.zip(codeRess.tail).forall { case (prev, cur) => prev.ctxs.isPrefixOf(cur.ctxs) })

    val subterms = codeRess.map(_.terminal)
    val terminal = cons(subterms)
    // TODO: Etendre ce check à d'autre cas (ensuring, etc.)
    assert(!isLambdaLike(terminal))

//    val composition = codeRess.foldLeft(Occurrences.empty)((usgs, cr) => usgs ++ Occurrences.of(cr.terminal)(using env, cr.ctxs))
    // TODO: C'est bien ctxs et pas cr.ctxs non?
    val composition = codeRess.foldLeft(Occurrences.empty)((usgs, cr) => usgs ++ Occurrences.of(cr.terminal)(using env, ctxs))
    val bdg = lb.getOrFresh()
    val ccc = varId2Var(bdg)
    val nme = ccc.toString
    CodeRes(terminal, composition, ctxs.addBoundDef(bdg, terminal, composition))
  }

  def combineCodeRes(codeRess: Seq[CodeRes], lb: LetBind)(cons: Seq[Code] => Signature)(using OEnv, Ctxs): CodeRes =
    combineCodeRes(codeRess, lb)(cs => codeOfSig(cons(cs), lb.tpe))

  def combineCodeRes(cr1: CodeRes, lb: LetBind)(cons: Code => Signature)(using env: OEnv): CodeRes =
    combineCodeRes(Seq(cr1), lb) { case Seq(c1) => codeOfSig(cons(c1), lb.tpe) } (using env, cr1.ctxs)

  def combineCodeRes(cr1: CodeRes, cr2: CodeRes, lb: LetBind)(cons: (Code, Code) => Signature)(using env: OEnv): CodeRes =
    combineCodeRes(Seq(cr1, cr2), lb) { case Seq(c1, c2) => codeOfSig(cons(c1, c2), lb.tpe) } (using env, cr2.ctxs)

  def freshVarId(name: String, tpe: Type): VarId = idOfVariable(Variable.fresh(name, tpe))

  object CodeRes {
    // TODO: Dire qu'est-ce que c'est que ce truc!!!!
    def of(term: Code)(using env: OEnv, ctxs: Ctxs): CodeRes =
      CodeRes(term, Occurrences.of(term), ctxs)

    def isTerminal(c: Code): Boolean = code2sig(c) match {
      // TODO: Ensuring?
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Decreases/* | Label.Ensuring*/ | Label.Let(_), _) => false
      case _ => true
    }

    def ifExpr(cond: CodeRes, thenn: CodeRes, els: CodeRes, lb: LetBind)(using env: OEnv): CodeRes = {
      assert(cond.ctxs.isPrefixOf(thenn.ctxs))
      assert(cond.ctxs.isPrefixOf(els.ctxs))
      // TODO: Pk ne pas mettre des UnboundDef pr les 2 branches? Ainsi, on pourra entièrement retirer composition de Ctx.Let -> non, pas aussi simple en cas de let v = lambda
      val occCond = Occurrences.of(cond.terminal)(using env, cond.ctxs)
      val (compThenn, cThenn) = thenn.selfPlugged(cond.ctxs)
      val (compEls, cEls) = els.selfPlugged(cond.ctxs)
      val terminal = codeOfSig(mkIfExpr(cond.terminal, cThenn, cEls), lb.tpe)
      val composition = occCond ++ compThenn ++ compEls
      val bdg = lb.getOrFresh("bdgIf")
      CodeRes(terminal, composition, cond.ctxs.addBoundDef(bdg, terminal, composition))
    }

    // For Lambda, Choose and Forall
    def lambdaLike(lab: Label.LambdaLike, body: CodeRes, lb: LetBind)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(body.ctxs))
      val (composition, cBody) = body.selfPlugged(ctxs)
      val terminal = codeOfSig(mkLambdaLike(lab, cBody), lb.tpe)

      val bdg = lb.getOrFresh("lam")
      val returned = {
        if (lab.isLambda) {
          codeOfVarId(ctxs.varBindingOf(terminal).getOrElse(bdg)) // varBindingOf: au cas ou c'est déjà bound
        } else terminal
      }
      CodeRes(returned, composition, ctxs.addBoundDef(bdg, terminal, composition))

      /*
      lb.v match {
        case Some(bdg) =>
          CodeRes(terminal, composition, ctxs.addBoundDef(bdg, terminal, composition))
        case None =>
          val bdg = lb.getOrFresh("lam")
          val returned = {
            if (lab.isLambda) {
              codeOfVarId(ctxs.varBindingOf(terminal).getOrElse(bdg)) // varBindingOf: au cas ou c'est déjà bound
            } else terminal
          }
          CodeRes(returned, composition, ctxs.addBoundDef(bdg, terminal, composition))
      }
      */
    }

    // TODO: On pourrait faire mieux (p.ex. extraire des trucs communs ds body pr en faire beneficier pred)
    def ensuring(body: CodeRes, pred: CodeRes, tpe: Type)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(pred.ctxs))
      assert(ctxs.isPrefixOf(body.ctxs))
      val (compBody, cBody) = body.selfPlugged(ctxs)
      val (compPred, cPred) = pred.selfPlugged(ctxs)
      val (comp, terminal) = code2sig(cPred) match {
        case Signature(Label.Lambda(_), Seq(`trueCode`)) => (compBody, cBody)
        case _ => (compBody ++ compPred, codeOfSig(mkEnsuring(cBody, cPred), tpe))
      }
      CodeRes(terminal, comp, ctxs)
    }

    def matchExpr(scrut: CodeRes, cases: Seq[CodeResMatchCase], lb: LetBind)(using env: OEnv): CodeRes = {
      assert(cases.nonEmpty)
      val terminal = codeOfSig(mkMatchExpr(scrut.terminal, cases.map(_.mc)), lb.tpe)
      val comp = cases.foldLeft(Occurrences.of(scrut.terminal)(using env, scrut.ctxs))(_ ++ _.composition)
      val bdg = lb.getOrFresh("bdgMatch")
      CodeRes(terminal, comp, scrut.ctxs.addBoundDef(bdg, terminal, comp))
    }
  }


  def codeOfExpr(e: Expr)(using OEnv, Ctxs): CodeRes = codeOfExpr(e, LetBind.empty(e.getType))

  def codeOfExpr(e: Expr, lb: LetBind)(using env: OEnv, ctxs: Ctxs): CodeRes = {
    val tpe = e.getType
    assert(tpe == lb.tpe)
    val res = e match {
      case v: Variable =>
        val vId = idOfVariable(v)
        val c = substByLet(vId).getOrElse(codeOfVarId(vId))
        CodeRes.of(c)

      case l: Literal[_] => CodeRes.of(codeOfLit(l))

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val ctxsThen = rcond.ctxs.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using env, ctxsThen)
        val ctxsEls = rcond.ctxs.withCond(negCodeOf(rcond.terminal)) // (using rcond.env)
        val rels = codeOfExpr(els)(using env, ctxsEls)
        CodeRes.ifExpr(rcond, rthenn, rels, lb)

      case e: (Lambda | Choose | Forall) =>
        val (lab: Label.LambdaLike, body) = e match {
          case Lambda(params, body) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (Label.Lambda(vParams), body)
          case Choose(res, pred) =>
            val vId = idOfVariable(res.toVariable)
            (Label.Choose(vId), pred)
          case Forall(params, pred) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (Label.Forall(vParams), pred)
        }
        val rbody = codeOfExpr(body)(using env.copy(inLambda = env.inLambda || lab.isLambda))
        CodeRes.lambdaLike(lab, rbody, lb)

      case Let(vd, e, body) =>
        val vId = idOfVariable(vd.toVariable)
        val re = codeOfExpr(e, LetBind.of(vId))
        assert(!code2sig(re.terminal).label.isEnsuring)
        val bodyEnv = code2sig(re.terminal).label match {
          case Label.Var(rvid) if rvid == vId =>
            assert(re.ctxs.boundTo(rvid).exists(isLambda))
            env
          case Label.Var(rvid) =>
            env.addVarSubst(vId, rvid)
          case Label.Lit(l) =>
            env.addLitSubst(vId, l)
          case _ =>
            re.ctxs.varBindingOf(re.terminal) match {
              case Some(`vId`) => env
              case Some(other) => env.addVarSubst(vId, other)
              case None => sys.error("Menteur :(")
            }
        }
        codeOfExpr(body, lb)(using bodyEnv, re.ctxs)

      case e: (Assume | Assert | Require | Decreases) =>
        val (lab: Label.AssumeLike, pred, body) = e match {
          case Assume(pred, body) => (Label.Assume, pred, body)
          case Assert(pred, _, body) => (Label.Assert, pred, body)
          case Require(pred, body) => (Label.Require, pred, body)
          case Decreases(measure, body) => (Label.Decreases, measure, body)
        }
        val rpred = codeOfExpr(pred)
        codeOfExpr(body, lb)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal, rpred.terminalComposition))

      case Ensuring(body, pred) =>
        // TODO: Ok?
        val rbody = codeOfExpr(body)
        val rpred = codeOfExpr(pred) // Using the default ctxs (not rbody.ctxs)
        CodeRes.ensuring(rbody, rpred, tpe)

      case ADT(id, tps, args) => codeOfExprsBound(args, lb)(mkADT(id, tps, _))
      case Tuple(args) => codeOfExprsBound(args, lb)(mkTuple)
      case FunctionInvocation(id, tps, args) => codeOfExprsBound(args, lb)(mkFunInvoc(id, tps, _))
      case Application(callee, args) => codeOfExprsBound(callee +: args, lb) { case cCallee +: cArgs => mkApp(cCallee, cArgs) }
      case IsConstructor(e, id) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, lb)(mkIsCtor(_, adt, id))
      case s @ ADTSelector(e, selector) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, lb)(mkADTSelector(_, adt, s.constructor, selector))

      // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
      // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
      //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
      //  une map ad-hoc qui contient ces infos...?
      case Annotated(e, flags) =>
        // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
        //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
        //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
        codeOfExprsBound(e, lb)(mkAnnot(_, flags))

      // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
      case and @ And(_) =>
        val ands = unAnd(and)
        codeOfExpr(Not(Or(ands.map(Not.apply))), lb)
      case or @ Or(_) => codeOfDisjunction(unOr(or), lb)
      case Not(e) => negExprOf(e, lb)

      case Implies(e1, e2) => codeOfExpr(Or(Not(e1), e2), lb)
      case Equals(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkEquals)
      case LessThan(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkLessThan)
      case GreaterThan(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkGreaterThan)
      case LessEquals(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkLessEquals)
      case GreaterEquals(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkGreaterEquals)
      case UMinus(e) => codeOfExprsBound(e, lb)(mkUMinus)
      case Plus(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkPlus)
      case Minus(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkMinus)
      case Times(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkTimes)
      case Division(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkDivision)
      case Remainder(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkRemainder)
      case Modulo(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkModulo)
      case BVNot(e) => codeOfExprsBound(e, lb)(mkBVNot)
      case BVAnd(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVAnd)
      case BVOr(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVOr)
      case BVXor(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVXor)
      case BVShiftLeft(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVShiftLeft)
      case BVAShiftRight(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVAShiftRight)
      case BVLShiftRight(e1, e2) => codeOfExprsBound(e1, e2, lb)(mkBVLShiftRight)
      case BVNarrowingCast(e, newTpe) => codeOfExprsBound(e, lb)(mkBVNarrowingCast(_, newTpe))
      case BVWideningCast(e, newTpe) => codeOfExprsBound(e, lb)(mkBVWideningCast(_, newTpe))
      case BVUnsignedToSigned(e) => codeOfExprsBound(e, lb)(mkBVUnsignedToSigned)
      case BVSignedToUnsigned(e) => codeOfExprsBound(e, lb)(mkBVSignedToUnsigned)
      case TupleSelect(e, index) => codeOfExprsBound(e, lb)(mkTupleSelect(_, index))
      case FiniteSet(elems, base) => codeOfExprsBound(elems, lb)(mkFiniteSet(_, base))
      case SetAdd(set, elem) => codeOfExprsBound(set, elem, lb)(mkSetAdd)
      case ElementOfSet(elem, set) => codeOfExprsBound(elem, set, lb)(mkElementOfSet)
      case SubsetOf(lhs, rhs) => codeOfExprsBound(lhs, rhs, lb)(mkSubsetOf)
      case SetIntersection(lhs, rhs) => codeOfExprsBound(lhs, rhs, lb)(mkSetIntersection)
      case SetUnion(lhs, rhs) => codeOfExprsBound(lhs, rhs, lb)(mkSetUnion)
      case SetDifference(lhs, rhs) => codeOfExprsBound(lhs, rhs, lb)(mkSetDifference)
      case FiniteArray(elems, base) => codeOfExprsBound(elems, lb)(mkFiniteArray(_, base))
      case LargeArray(elems, default, size, base) => ???
      case ArraySelect(array, index) => codeOfExprsBound(array, index, lb)(mkArraySelect)
      case ArrayUpdated(array, index, v) => codeOfExprsBound(array, index, v, lb)(mkArrayUpdated)
      case ArrayLength(array) => codeOfExprsBound(array, lb)(mkArrayLength)

      // TODO: Quid lb???
      case Error(ofTpe, descr) =>
        CodeRes.of(codeOfSig(mkError(ofTpe, descr), lb.tpe))
      case NoTree(ofTpe) =>
        CodeRes.of(codeOfSig(mkNoTree(ofTpe), lb.tpe))

      // TODO: Passer en revue la pureté: p.ex. si on est pas exhaustif, devrait-on retourner "assumeChecked"?
      case MatchExpr(scrut, cases) =>
        // Ici, on fait qqchose de similaire au IfExpr
        val rscrut = codeOfExpr(scrut)
        assert(codeTpe(rscrut.terminal) == scrut.getType, s"${codeTpe(rscrut.terminal)} != ${scrut.getType}")
        val rcases = signatureOfCases(rscrut.terminal, cases, Seq.empty)(using env, rscrut.ctxs)
        CodeRes.matchExpr(rscrut, rcases, lb)

      case e =>
        println("computeSignature: Do not know how to handle "+e)
        ???
    }
    assert(ctxs.isPrefixOf(res.ctxs))
    simplifyTopLvl(res, lb)
  }

  case class CodeResMatchCase(mc: LabMatchCase, composition: Occurrences)
  case class PatternExprRes(pat: LabelledPattern, bdgs: Seq[(VarId, Code)], patConds: Seq[Code])

  def signatureOfPatternExpr(scrut: Code, pat: Pattern)(using env: OEnv, ctxs: Ctxs): PatternExprRes = {
//    val bdg: Option[VarId] = pat.binder.map(vd => idOfVariable(vd.toVariable))
//    val bdgs1 = bdg.map(v => Seq((v, scrut))).getOrElse(Seq.empty)
    // TODO: Rework match scrut bdgs
    val bdg: VarId = pat.binder.map(vd => idOfVariable(vd.toVariable)).getOrElse(freshVarId("scrut", codeTpe(scrut)))
    val bdgs1 = Seq((bdg, scrut))
    pat match {
      case WildcardPattern(_) => PatternExprRes(LabelledPattern.Wildcard(Some(bdg)), bdgs1, Seq.empty)

      case ADTPattern(_, id, tps, subps) =>
        val adt = ADTType(id, tps)
        val conds1 = {
          if (isConstructor(scrut, adt,id) == Some(true)) Seq.empty[Code]
          else Seq(codeOfSig(mkIsCtor(scrut, adt, id), BoolTy))
        }
        val subscruts = adtSubscrutinees(scrut, adt)
        assert(subscruts.size == subps.size)

        val (labSubPats, bdgs2, conds2) = subscruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, conds1)) {
          // TODO: Annoté en dropvc?
          case ((labSubPatAcc, bdgsAcc, condsAcc), (subscrut, subpat)) =>
            // TODO: Env avec conds accumulées ok?
            val PatternExprRes(labSubPat, newBdgs, newConds) =
              signatureOfPatternExpr(subscrut, subpat)(using env, ctxs.withConds(condsAcc))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        PatternExprRes(LabelledPattern.ADT(Some(bdg), id, tps, labSubPats), bdgs2, conds2)

      case TuplePattern(_, subps) =>
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        assert(subscruts.size == subps.size)

        val (labSubPats, bdgs2, conds) = subscruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, Seq.empty[Code])) {
          case ((labSubPatAcc, bdgsAcc, condsAcc), (subscrut, subpat)) =>
            // TODO: Env avec conds accumulées ok?
            val PatternExprRes(labSubPat, newBdgs, newConds) =
              signatureOfPatternExpr(subscrut, subpat)(using env, ctxs.withConds(condsAcc))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        PatternExprRes(LabelledPattern.TuplePattern(Some(bdg), labSubPats), bdgs2, conds)

      case LiteralPattern(_, lit) => PatternExprRes(LabelledPattern.Lit(Some(bdg) ,lit), bdgs1, Seq.empty)

      case UnapplyPattern(_, recs, id, tps, subps) =>
        // TODO: !!!! Si on utilise codeOf, ne pas oublier d'utiliser le subst approprié !!!
        sys.error(s"Does not know how to handle $pat")
    }
  }

  def signatureOfCase(cScrut: Code, mc: MatchCase)(using env: OEnv, ctxs: Ctxs): (CodeResMatchCase, Seq[Code]) = {
    // patConds: sans le guard!
    val PatternExprRes(labPat, bdgs, patConds) = signatureOfPatternExpr(cScrut, mc.pattern)
    val guardCtxs = addScrutineeBindings(ctxs, bdgs).withConds(patConds)
    // TODO: On pourrait conserver le ctx des guard pour le body? En gros, qu'on plug le body dans le ctx de guard

    // Comme pour les ifs, on ne hoist rien des branches

    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using env, guardCtxs))
    val (compGuard, cGuard) = rguard.map(_.selfPlugged(ctxs)).getOrElse((Occurrences.empty, trueCode))

    val rhsCtxs = guardCtxs.withCond(cGuard)
    val rrhs = codeOfExpr(mc.rhs)(using env, rhsCtxs)
    val (compRhs, rhs) = rrhs.selfPlugged(ctxs)

    val labMc = LabMatchCase(labPat, cGuard, rhs)
    (CodeResMatchCase(labMc, compGuard ++ compRhs), patConds :+ cGuard)
  }

  def signatureOfCases(cScrut: Code, mcs: Seq[MatchCase], acc: Seq[CodeResMatchCase])
                      (using env: OEnv, ctxs: Ctxs): Seq[CodeResMatchCase] = {
    if (mcs.isEmpty) acc
    else {
      val (newMatchCase, caseConds) = signatureOfCase(cScrut, mcs.head)
      val negCaseConds = negatedConjunction(caseConds)
      signatureOfCases(cScrut, mcs.tail, acc :+ newMatchCase)(using env, ctxs.withCond(negCaseConds))
    }
  }

  def checkForContradiction(disj: Seq[Code])(using OEnv, Ctxs): Boolean = {
    // TODO: Relativement different par rapport à l'orig
    val (pos, neg) = disj.foldLeft((Set.empty[Code], Set.empty[Code])) {
      case ((posAcc, negAcc), c) =>
        // TODO: Hmm, il faudrait aussi faire pour les <=, <, >= et > ?
        // TODO: Hmm, il faudrait aussi faire pour les <=, <, >= et > ?
        // TODO: Hmm, il faudrait aussi faire pour les <=, <, >= et > ?
        code2sig(c) match {
          case Signature(Label.Not, Seq(cc)) => (posAcc, negAcc + cc)
          case _ => (posAcc + c, negAcc)
        }
    }

    if (pos.intersect(neg).nonEmpty) true
    else {
      neg.exists { negC =>
        code2sig(negC) match {
          case Signature(Label.Or, negDisj) =>
            // TODO: Est-ce vrai? Quid si un meme code apparait dans un truc negatif?
            negDisj.forall(disj.contains)
          case _ => false
        }
      }
    }
  }

//  // TODO: Ok?
//  def pDisj(e: Expr)(using OEnv): Seq[Code] = {
//    ???
//    assert(e.getType == BoolTy, s"Got ${e.getType}")
//    sigOfExpr(e) match {
//      case Signature(Label.Or, children) => children // TODO: Flatten more?
//      case Signature(Label.Not, Seq(c)) => Seq(codeOfSig(pNegNormal(c), BoolTy)) // TODO: Ok?
//      case sig => Seq(codeOfSig(sig, BoolTy))
//    }
//  }

  def codeOfDisjunction(disjs: Seq[Expr], lb: LetBind)(using env: OEnv, outerCtxs: Ctxs): CodeRes = {
    assert(disjs.forall(_.getType == BoolTy))
    assert(lb.tpe == BoolTy)
    val (_, composition, cArgs) = disjs.foldLeft((outerCtxs, Occurrences.empty, Seq.empty[Code])) {
      // Remarque: ctxs ne contient que les negations accumulées, pas de binding!
      case ((ctxs, compAcc, cArgsAcc), e) =>
        assert(outerCtxs.isPrefixOf(ctxs))
        assert(outerCtxs.bindings == ctxs.bindings)

        given Ctxs = ctxs
        val re = codeOfExpr(e)
        assert(codeTpe(re.terminal) == BoolTy, s"Got ${codeTpe(re.terminal)}")
        // TODO: Essayer d'extraire autant que possible ici
        // Remarque: c'est bien le ctxs d'origine qu'on utilise,
        // pas celui de re car celui-ci contient des bdgs et d'autres conds (qui ne sont pas carry over)
        val (occ, rePlugged) = re.selfPlugged(outerCtxs)
        // Ditto ici
        val newCtxs = outerCtxs.withCond(negCodeOf(rePlugged))
        (newCtxs, compAcc ++ occ, cArgsAcc :+ rePlugged)
    }
    val isPure = cArgs.forall(c => codePurity(c).isPure)
    val cOr = simplifiedDisjunction(cArgs, mayDrop = isPure, mayReorder = isPure)
    unplugged(cOr) match {
      case Some((cr, _)) => cr // TODO: Mais c'est dégueulasse !!!! Et c'est quoi la justification au juste?????
      case None =>
        // Remarque: on retourne le ctx original car les PCs des ors ne sont pas retenues hors des disjunctions.
        // P.ex. dans val x = b1 || b2 || b3 il serait insensé d'avoir !b1 && !b2 && !b3 dans le env de x.
        val bdg = lb.getOrFresh("orBdg")
        // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
        // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
        // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
        // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
        // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
        val actualComp = composition
        CodeRes(cOr, actualComp, outerCtxs.addBoundDef(bdg, cOr, actualComp))
    }
  }

  // TODO: Voir si on peut pas faire qqchose pr eviter code dup avec pNegNormal
  // Signature de Not(child)
  def negExprOf(child: Expr, lb: LetBind)(using env: OEnv, ctxs: Ctxs): CodeRes = {
    assert(child.getType == BoolTy && lb.tpe == BoolTy)

    child match {
      case Not(e) => codeOfExpr(e)
      case LessThan(lhs, rhs) => codeOfExpr(GreaterEquals(lhs, rhs))
      case GreaterEquals(lhs, rhs) => codeOfExpr(LessThan(lhs, rhs))
      case GreaterThan(lhs, rhs) => codeOfExpr(LessEquals(lhs, rhs))
      case LessEquals(lhs, rhs) => codeOfExpr(GreaterThan(lhs, rhs))
      // TODO: Comme on ne peut pas faire grand chose de spécial, c'est "envoyé" au codeOfExpr
      /*
      case or @ Or(_) =>
        // TODO: Rappel: il est interdit de sort
        // TODO: Ici, on fait un filter.distinct, ce que l'orig ne fait pas vraiment?
        val ors = unOr(or).sortBy(sizeOf)
        val r = ors.tail.flatMap(pDisj)
          .filter(_ != falseCode)
          .distinct
        if (r.isEmpty) negExprOf(ors.head)
        else {
          // TODO: Ok?
          // TODO: Ressemble pas mal à simplifiedDisjunction
          val s = (pDisj(ors.head) ++ r)
            .filter(_ != falseCode).distinct
          val purity = fold(s.map(codePurity))
          if (purity.isPure && (s.contains(trueCode) || checkForContradiction(s))) falseSig
          else if (s.size == 1) pNegNormal(s.head)
          else mkNot(codeOfSig(mkOr(s), BoolTy))
        }
      */
      case _ =>
        val rchild = codeOfExpr(child)
        val negChild = negCodeOf(rchild.terminal)
        if (rchild.ctxs.isBoundDef(negChild)) rchild.derivedFromCtxs(negChild)
        else {
          // Dans Not(child), on doit compter child, mais pas Not(child)
//          rchild.derived(negChild, rchild.terminalComposition ++ Occurrences.of(rchild.terminal)(using env, rchild.ctxs))
          assert(code2sig(rchild.terminal).label.isLitOrVar || rchild.ctxs.isBoundDef(rchild.terminal))
          rchild.derived(negChild, Occurrences.of(rchild.terminal)(using env, rchild.ctxs))
        }
      }
  }

  def freshened(v: VarId): VarId = idOfVariable(varId2Var(v).freshen)

  def codeOfSig(sig: Signature, tpe: Type): Code = {
    sig2code.get(sig) match {
      case Some(c) =>
        assert(codeTpe(c) == tpe, s"${codeTpe(c)} != $tpe")
        c
      case None =>
        val newCode = Code.fromInt(sig2code.size)
        assert(!code2sig.contains(newCode))
        sig2code += sig -> newCode
        code2sig += newCode -> sig
        codeTpe += newCode -> tpe
        newCode
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def implied(rhs: Code)(using env: OEnv, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode) true
    else if (ctxs.allConds.isEmpty) false // car rhs != trueCode
    else {
      // TODO: Quid pureté de rhs???
      // TODO: Pourrait-on envisager de cache env.condition?
      // a ==> b === a && b = a
      // TODO: Drop+Reorder ok?
      // TODO: C'est un peu bête parce que conjunct utilise ctxs...
      val lhsConj = conjunct(ctxs.allConds, mayDrop = true, mayReorder = true)
      val rhsLhsConj = conjunct(Seq(lhsConj, rhs), mayDrop = true, mayReorder = true)
      rhsLhsConj == lhsConj
    }
  }

  // Is `c` an ADT with constructor `id`?
  //   Some(true) - Yes
  //   Some(false) - No
  //   None - Can't tell
  def isConstructor(c: Code, adt: ADTType, id: Identifier)(using OEnv, Ctxs): Option[Boolean] = {
    // TODO: What about purity?
    def codeIsCtor(ofId: Identifier): Code =
      codeOfSig(Signature(Label.IsConstructor(adt, ofId), Seq(c)), BoolTy)
    def codeNotCtor(ofId: Identifier): Code =
      negCodeOf(codeIsCtor(ofId))

    code2sig(c) match {
      case Signature(Label.ADT(id2, _), _) => Some(id == id2)
      case _ =>
        if (implied(codeIsCtor(id))) Some(true)
        else if (implied(codeNotCtor(id))) Some(false)
        else {
          val cons = getConstructor(id, adt.tps)
          val sort = cons.sort
          // All other constructors (excluding `id`) for the ADT
          val alts = (sort.constructors.toSet - cons).map(_.id)

          if (alts.exists(alt => implied(codeIsCtor(alt)))) Some(false)
          else if (alts.forall(alt => implied(codeNotCtor(alt)))) Some(true)
          else None
        }
    }
  }

  def idOfVariable(v: Variable): VarId = var2VarId.get(v) match {
    case Some(vId) => vId
    case None =>
      val vId = VarId.fromInt(varIdCounter)
      varIdCounter += 1
      var2VarId += v -> vId
      varId2Var += vId -> v
      vId
  }
  def varTpe(v: VarId): Type = varId2Var(v).getType // TODO: Apparemment, il y a une difference entre .getType et .tpe (pour les refinement type)

  // TODO: Renommer, risque de confusion...
  def conjunct(conj: Seq[Code])(using OEnv, Ctxs): Code = {
    val isPure = conj.forall(c => codePurity(c).isPure)
    conjunct(conj, isPure, isPure)
  }

  def conjunct(conj: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, Ctxs): Code = negCodeOf(negatedConjunction(conj, mayDrop, mayReorder))

  def negatedConjunction(conj: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, Ctxs): Code= simplifiedDisjunction(conj.map(negCodeOf), mayDrop, mayReorder)

  // TODO: Renommer, risque de confusion...
  def negatedConjunction(conj: Seq[Code])(using OEnv, Ctxs): Code= {
    val isPure = conj.forall(c => codePurity(c).isPure)
    negatedConjunction(conj, isPure, isPure)
  }

  def codeOfIntLit(lit: BigInt, tpe: Type): Code = codeOfLit(intLitOfType(lit, tpe))

  def intLitOfType(lit: BigInt, tpe: Type): Literal[_] = tpe match {
    case IntegerType() => IntegerLiteral(lit)
    case RealType() => FractionLiteral(lit, 1)
    case BVType(signed, size) =>
      // BVLiteral guards against signed=true and lit < 0, but not against lit not fitting
      // into the given bitwidth (it wrap-around)
      val (loIncl, hiExcl) = {
        if (signed) (-BigInt(2).pow(size-1), BigInt(2).pow(size-1))
        else (BigInt(0), BigInt(2).pow(size))
      }
      if (!(loIncl <= lit && lit < hiExcl)) {
        sys.error(s"$lit does not fit into $tpe  (with range [$loIncl, $hiExcl[)")
      }
      BVLiteral(signed, lit, size)
    case _ => sys.error(s"$tpe is not an integer-like type")
  }

  /*
  def simpForall(nbParams: Int, body: Code)(using subst: Subst): Signature = {
    def liftForall(es: Seq[Code]): Signature = {
      // TODO: Il faudra incrémenter les indexed vars des forall
      val (nbParamss, bodies) = es.map(c => code2sig(c) match {
        case Signature(Label.Forall(nbParams2), body2) => (nbParams2, ???) // TODO: Qqchose à faire par rapport aux indexed vars???
        case s => (0, s)
      }).unzip
      val allParams = nbParams + nbParamss.sum
      val combinedBody = ???
      if (allParams == nbParams) Signature(Label.Forall(nbParams), combinedBody)
      else simpForall(allParams, combinedBody)
    }

    code2sig(body) match {
      case Signature(Label.Forall(nbParams2), Seq(body2)) => simpForall(nbParams + nbParams2, body2)
      // TODO: On n'a pas de And ou Implies!!! On devrait pouvoir les "reconstruire"
      case Signature(Label.Or, disjs) => ???
      case _ => Signature(Label.Forall(nbParams), Seq(body))
    }
  }
  */

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class RevEnv(revLetDefs: Map[Code, VarId]) {
    def withLetBounds(vs: Seq[(VarId, Code)]): RevEnv =
      RevEnv(revLetDefs ++ vs.map { case (v, c) => c -> v }.toMap)

    def withLetBounds(v: VarId, c: Code): RevEnv =
      RevEnv(revLetDefs + (c -> v))
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty)
  }

  case class RevRes(expr: Expr, used: Set[VarId])

  def uncodeOf(c: Code)(using renv: RevEnv): RevRes = {
    renv.revLetDefs.get(c) match {
      case Some(vIx) =>
        return RevRes(varId2Var(vIx), Set(vIx))
      case None => ()
    }

    code2sig(c) match {
      case Signature(Label.Var(v), Seq()) => RevRes(varId2Var(v), Set(v))
      case Signature(Label.Lit(lit), Seq()) => RevRes(lit, Set.empty)
      case Signature(Label.Tuple, args) => recHelper(args)(Tuple.apply)
      case Signature(Label.ADT(id, tps), args) => recHelper(args)(ADT(id, tps, _))
      case Signature(Label.ADTSelector(_, _, sel), Seq(recv)) => recHelper(recv)(ADTSelector(_, sel))
      case Signature(Label.FunctionInvocation(id, tps), args) => recHelper(args)(FunctionInvocation(id, tps, _))
      case Signature(Label.Annotated(flags), Seq(e)) => recHelper(e)(Annotated(_, flags))
      case Signature(Label.IsConstructor(_, id), Seq(e)) => recHelper(e)(IsConstructor(_, id))
      case Signature(Label.Application, all@(callee +: args)) =>
        recHelper(all) { case callee +: args => Application(callee, args) }

      case Signature(Label.Let(v), Seq(cE, cBody)) =>
        val e = uncodeOf(cE)
        val body = uncodeOf(cBody)(using renv.withLetBounds(v, cE))
        RevRes(Let(new ValDef(varId2Var(v)), e.expr, body.expr), e.used ++ body.used)

      // TODO: Ok?
      case Signature(Label.Assume, Seq(pred, body)) => recHelper(pred, body)(Assume.apply)
      case Signature(Label.Assert, Seq(pred, body)) => recHelper(pred, body)(Assert(_, None, _))
      case Signature(Label.Require, Seq(pred, body)) => recHelper(pred, body)(Require.apply)
      case Signature(Label.Ensuring, Seq(body, pred)) =>
        recHelper(body, pred) { case (body, pred: Lambda) => Ensuring(body, pred) }
      case Signature(Label.Decreases, Seq(measure, body)) => recHelper(measure, body)(Decreases.apply)

      case Signature(Label.IfExpr, Seq(cond, thn, els)) => recHelper(cond, thn, els)(IfExpr.apply)
      case Signature(Label.Lambda(params), Seq(body)) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        recHelper(body)(Lambda(vds, _))
      case Signature(Label.Choose(v), Seq(pred)) => recHelper(pred)(Choose(new ValDef(varId2Var(v)), _))
      case Signature(Label.Forall(params), Seq(pred)) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        recHelper(pred)(Forall(vds, _))

      case Signature(Label.Or, args) => recHelper(args)(Or.apply)
      case Signature(Label.Not, Seq(c)) =>
        code2sig(c) match {
          case Signature(Label.Or, disjs) => recHelper(disjs.map(negCodeOf))(And.apply)
          case _ => recHelper(c)(Not.apply)
        }
      case Signature(Label.Equals, Seq(c1, c2)) => recHelper(c1, c2)(Equals.apply)
      case Signature(Label.LessThan, Seq(c1, c2)) => recHelper(c1, c2)(LessThan.apply)
      case Signature(Label.GreaterThan, Seq(c1, c2)) => recHelper(c1, c2)(GreaterThan.apply)
      case Signature(Label.LessEquals, Seq(c1, c2)) => recHelper(c1, c2)(LessEquals.apply)
      case Signature(Label.GreaterEquals, Seq(c1, c2)) => recHelper(c1, c2)(GreaterEquals.apply)
      case Signature(Label.UMinus, Seq(c)) => recHelper(c)(UMinus.apply)
      case Signature(Label.Plus, Seq(c1, c2)) => recHelper(c1, c2)(Plus.apply)
      case Signature(Label.Minus, Seq(c1, c2)) => recHelper(c1, c2)(Minus.apply)
      case Signature(Label.Times, Seq(c1, c2)) => recHelper(c1, c2)(Times.apply)
      case Signature(Label.Division, Seq(c1, c2)) => recHelper(c1, c2)(Division.apply)
      case Signature(Label.Remainder, Seq(c1, c2)) => recHelper(c1, c2)(Remainder.apply)
      case Signature(Label.Modulo, Seq(c1, c2)) => recHelper(c1, c2)(Modulo.apply)
      case Signature(Label.BVNot, Seq(c)) => recHelper(c)(BVNot.apply)
      case Signature(Label.BVAnd, Seq(c1, c2)) => recHelper(c1, c2)(BVAnd.apply)
      case Signature(Label.BVOr, Seq(c1, c2)) => recHelper(c1, c2)(BVOr.apply)
      case Signature(Label.BVXor, Seq(c1, c2)) => recHelper(c1, c2)(BVXor.apply)
      case Signature(Label.BVShiftLeft, Seq(c1, c2)) => recHelper(c1, c2)(BVShiftLeft.apply)
      case Signature(Label.BVAShiftRight, Seq(c1, c2)) => recHelper(c1, c2)(BVAShiftRight.apply)
      case Signature(Label.BVLShiftRight, Seq(c1, c2)) => recHelper(c1, c2)(BVLShiftRight.apply)
      case Signature(Label.BVNarrowingCast(newType), Seq(c)) => recHelper(c)(BVNarrowingCast(_, newType))
      case Signature(Label.BVWideningCast(newType), Seq(c)) => recHelper(c)(BVWideningCast(_, newType))
      case Signature(Label.BVUnsignedToSigned, Seq(c)) => recHelper(c)(BVUnsignedToSigned.apply)
      case Signature(Label.BVSignedToUnsigned, Seq(c)) => recHelper(c)(BVSignedToUnsigned.apply)
      case Signature(Label.TupleSelect(index), Seq(c)) => recHelper(c)(TupleSelect(_, index))

      case Signature(Label.FiniteSet(base), args) => recHelper(args)(FiniteSet(_, base))
      case Signature(Label.SetAdd, Seq(set, elem)) => recHelper(set, elem)(SetAdd.apply)
      case Signature(Label.ElementOfSet, Seq(elem, set)) => recHelper(elem, set)(ElementOfSet.apply)
      case Signature(Label.SubsetOf, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SubsetOf.apply)
      case Signature(Label.SetIntersection, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetIntersection.apply)
      case Signature(Label.SetUnion, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetUnion.apply)
      case Signature(Label.SetDifference, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetDifference.apply)

      case Signature(Label.FiniteArray(base), args) => recHelper(args)(FiniteArray(_, base))
      case Signature(Label.LargeArray(elemsIndices, base), all@(elems :+ default :+ size)) =>
        recHelper(all) { case elems :+ default :+ size =>
          LargeArray(elemsIndices.zip(elems).toMap, default, size, base)
        }
      case Signature(Label.ArraySelect, Seq(arr, i)) => recHelper(arr, i)(ArraySelect.apply)
      case Signature(Label.ArrayUpdated, Seq(arr, i, v)) => recHelper(arr, i, v)(ArrayUpdated.apply)
      case Signature(Label.ArrayLength, Seq(arr)) => recHelper(arr)(ArrayLength.apply)

      case Signature(Label.Error(tpe, descr), Seq()) => RevRes(Error(tpe, descr), Set.empty)
      case Signature(Label.NoTree(tpe), Seq()) => RevRes(NoTree(tpe), Set.empty)

      case Signature(Label.MatchExpr(pats), cScrut +: cGuardRhs) =>
        assert(2 * pats.size == cGuardRhs.size)


        def convertPattern(pat: LabelledPattern, usedBdgs: Set[VarId]): Pattern = {
          val bdg = pat.bdg.filter(usedBdgs).map(v => new ValDef(varId2Var(v)))
          pat match {
            case LabelledPattern.Wildcard(_) => WildcardPattern(bdg)
            case LabelledPattern.ADT(_, id, tps, sub) => ADTPattern(bdg, id, tps, sub.map(convertPattern(_, usedBdgs)))
            case LabelledPattern.TuplePattern(_, sub) => TuplePattern(bdg, sub.map(convertPattern(_, usedBdgs)))
            case LabelledPattern.Lit(_, lit) => LiteralPattern(bdg, lit)
            case LabelledPattern.Unapply(_, recs, id, tps, sub) => ???
          }
        }

        def uncodeOfCase(pat: LabelledPattern, cGuard: Code, cRhs: Code): (Pattern, RevRes, RevRes) = {
          val scrutBdgs = allScrutinees(cScrut, pat)
          val newRenv = renv.withLetBounds(scrutBdgs)
          val guard = uncodeOf(cGuard)(using newRenv)
          val rhs = uncodeOf(cRhs)(using newRenv)
          // On retire les scrut. binding qui sont inutiles.
          val usedBdgs = scrutBdgs.map(_._1).filter(v => guard.used(v) || rhs.used(v)).toSet
          (convertPattern(pat, usedBdgs), guard, rhs)
        }
        val (guards, rhss) = cGuardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val scrut = uncodeOf(cScrut)
        val (cases, used) = pats.zip(guards).zip(rhss).foldLeft((Seq.empty[MatchCase], scrut.used)) {
          case ((accCases, accUsed), ((labPat, cGuard), cRhs)) =>
            val (pat, guard, rhs) = uncodeOfCase(labPat, cGuard, cRhs)
            val cse = MatchCase(pat, if (guard.expr == BooleanLiteral(true)) None else Some(guard.expr), rhs.expr)
            (accCases :+ cse, accUsed ++ guard.used ++ rhs.used)
        }
        RevRes(MatchExpr(scrut.expr, cases), used)

      case sig =>
        sys.error(s"uncodeOf: what is this: $sig")
    }
  }

  def recHelper(args: Seq[Code])(recons: Seq[Expr] => Expr)(using RevEnv): RevRes = {
    val rargs = args.map(uncodeOf)
    RevRes(recons(rargs.map(_.expr)), rargs.flatMap(_.used).toSet)
  }
  def recHelper(c1: Code)(recons: Expr => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1)) { case Seq(e1) => recons(e1) }
  def recHelper(c1: Code, c2: Code)(recons: (Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2)) { case Seq(e1, e2) => recons(e1, e2) }
  def recHelper(c1: Code, c2: Code, c3: Code)(recons: (Expr, Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2, c3)) { case Seq(e1, e2, e3) => recons(e1, e2, e3) }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def b2c(b: Boolean): Code = if (b) trueCode else falseCode
  def b2sig(b: Boolean): Signature = if (b) trueSig else falseSig

  val assmChkPurity: Purity = if (opts.assumeChecked) Pure else Impure

  def unAnd(e: Expr): Seq[Expr] = e match {
    case And(es) => es.flatMap(unAnd)
    case e => Seq(e)
  }

  def unOr(e: Expr): Seq[Expr] = e match {
    case Or(es) => es.flatMap(unOr)
    case e => Seq(e)
  }

  def unOrCodes(disjs: Seq[Code]): Seq[Code] = disjs.flatMap(unOrCode)

  def unOrCode(c: Code): Seq[Code] = code2sig(c) match {
    case Signature(Label.Or, disjs) => disjs.flatMap(unOrCode)
    case _ => Seq(c)
  }

  def sizeOf(e: Expr): Int = sizeCache.getOrElseUpdate(e, exprOps.formulaSize(e))

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def fnPurity(fn: Identifier): Purity = {
    def resolvedPurity(isPure: Boolean): Unit = {
      purityCache += fn -> isPure
      if (blocking.contains(fn)) {
        val (blockedFns, blockedCodes) = blocking.remove(fn).get
        for (blockedFn <- blockedFns) {
          assert(fnBlockedBy.contains(blockedFn))
          assert(fnBlockedBy(blockedFn) == Set(fn))
          fnBlockedBy -= blockedFn
          purityCache += blockedFn -> isPure
        }
        for (blockedCode <- blockedCodes) {
          assert(codeBlockedBy.contains(blockedCode))
          assert(codeBlockedBy(blockedCode) == Set(fn))
          codeBlockedBy -= blockedCode
          codePurityCache += blockedCode -> isPure // TODO: env dependant?
        }
      }
    }
    def addToBlocked(blockers: Set[Identifier]): Unit = {
      assert(!blockers.contains(fn))
      // On s'ajoute à la liste des bloqués
      fnBlockedBy += fn -> blockers
      for (blocker <- blockers) {
        val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
        blocking += blocker -> (blockedFns + fn, blockedCodes)
      }

      // On upd. les bloqués pour qu'ils pointent vers ceux qui nous bloquent, et pas nous.
      val (blockedFnsByThisFn, blockedCodeByThisCode) = blocking.remove(fn).getOrElse((Set.empty, Set.empty))
      for (blockedFn <- blockedFnsByThisFn) {
        assert(fnBlockedBy.contains(blockedFn))
        val upd = fnBlockedBy(blockedFn) - fn ++ blockers
        fnBlockedBy += blockedFn -> upd
      }
      for (blockedCode <- blockedCodeByThisCode) {
        assert(codeBlockedBy.contains(blockedCode))
        val upd = codeBlockedBy(blockedCode) - fn ++ blockers
        codeBlockedBy += blockedCode -> upd
      }
    }

    if (visiting.contains(fn)) {
      if (!opts.assumeChecked) Impure
      else Delayed(Set(fn))
    } else {
      purityCache.get(fn) match {
        case Some(true) => Pure
        case Some(false) => Impure
        case None if fnBlockedBy.contains(fn) => Delayed(fnBlockedBy(fn))
        case None =>
          // TODO: Quid condition venant du simplifier (s'il y en as???)?
          // TODO: Différencier:
          //    -outer assms et local assms
          //    -outer open bound et local open bound
          given OEnv = OEnv(Map.empty, inLambda = false, forceBinding = true)
          given Ctxs = Ctxs.empty
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val bodyCodeRes = codeOfExpr(getFunction(fn).fullBody)
          val bodyCode = bodyCodeRes.selfPlugged(Ctxs.empty)._2
          val purity = codePurity(bodyCode)
          visiting -= fn
          purity match {
            case Pure =>
              resolvedPurity(isPure = true)
              Pure
            case Impure =>
              resolvedPurity(isPure = false)
              Impure
            case Delayed(blockers0) =>
              assert(blockers0.nonEmpty)
              assert(opts.assumeChecked)
              assert(!fnBlockedBy.contains(fn))
              val blockersWoCurr = blockers0 - fn

              if (blockers0.contains(fn)) {
                assert(blocking.contains(fn))
                if (blockersWoCurr.isEmpty) {
                  resolvedPurity(isPure = true)
                  Pure
                } else {
                  addToBlocked(blockersWoCurr)
                  Delayed(blockersWoCurr)
                }
              } else {
                assert(!blocking.contains(fn))
                addToBlocked(blockers0)
                Delayed(blockers0)
              }
          }
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def adtSubscrutinees(scrut: Code, adt: ADTType): Seq[Code] = {
    val tcons = getConstructor(adt.id, adt.tps)
    tcons.fields.map(fld => codeOfSig(mkADTSelector(scrut, adt, tcons, fld.id), fld.getType))
  }

  def tupleSubscrutinees(scrut: Code, tt: TupleType): Seq[Code] = {
    tt.bases.zipWithIndex.map { case (base, i) => codeOfSig(mkTupleSelect(scrut, i + 1), base) }
  }

  def allScrutinees(scrut: Code, pat: LabelledPattern): Seq[(VarId, Code)] = {
    val slf = pat.bdg.map(_ -> scrut).toSeq
    pat match {
      case LabelledPattern.Wildcard(_) | LabelledPattern.Lit(_, _) => slf
      case LabelledPattern.ADT(_, id, tps, subps) =>
        val subscruts = adtSubscrutinees(scrut, ADTType(id, tps))
        assert(subscruts.size == subps.size)
        slf ++ subscruts.zip(subps).flatMap {
          case (subscrut, subp) => allScrutinees(subscrut, subp)
        }
      case LabelledPattern.TuplePattern(_, subps) =>
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        assert(subscruts.size == subps.size)
        slf ++ subscruts.zip(subps).flatMap {
          case (subscrut, subp) => allScrutinees(subscrut, subp)
        }
      case LabelledPattern.Unapply(scrut0, recs, id, tps, sub) => sys.error("Oh non, un Unapply :(")
    }
  }

  def addScrutineeBindings(ctxs: Ctxs, bdgs: Seq[(VarId, Code)])(using env: OEnv): Ctxs = {
    bdgs.foldLeft(ctxs) {
      case (ctxs, (v, c)) =>
        // TODO: Rework match scrut bdgs
        if (code2sig(c).label.isLitOrVar) ctxs
        else ctxs.addBoundDef(v, c, Occurrences.of(c)(using env, ctxs))
    }
  }

  // TODO: Ordre ok???
  // TODO: Ordre ok???
  // TODO: Ordre ok???
  // TODO: Env: faut-il ajouter les bdgs intérmediaire????
  // TODO: Env: faut-il ajouter les bdgs intérmediaire????
  // TODO: Env: faut-il ajouter les bdgs intérmediaire????
  // TODO: Env: faut-il ajouter les bdgs intérmediaire????
  def collectPatternConds(scrut: Code, pat: LabelledPattern, recursive: Boolean)(using env: OEnv, ctxs: Ctxs): Seq[Code] = pat match {
    case LabelledPattern.Wildcard(_) | LabelledPattern.Lit(_, _) => Seq.empty
    case LabelledPattern.ADT(_, id, tps, subps) =>
      val adt = ADTType(id, tps)
      val tcons = getConstructor(id, tps)
      assert(tcons.fields.size == subps.size)
      val patConds = {
        if (isConstructor(scrut, adt, id) == Some(true)) Seq.empty[Code]
        else Seq(codeOfSig(mkIsCtor(scrut, adt, id), BoolTy))
      }
      val subconds = {
        if (recursive) {
          val subscruts = adtSubscrutinees(scrut, adt)
          assert(subscruts.size == subps.size)
          subscruts.zip(subps).flatMap {
            // TODO: env with cond ok?
            // TODO: Il faut accumuler les conds dans env!!!
            case (subscrut, subpat) =>
              collectPatternConds(subscrut, subpat, true)(using env, ctxs.withConds(patConds))
          }
        } else Seq.empty
      }
      patConds ++ subconds
    case LabelledPattern.TuplePattern(_, subps) =>
      if (recursive) {
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        assert(subscruts.size == subps.size)
        subscruts.zip(subps).flatMap {
          // TODO: Il faut accumuler les conds dans env!!!
          case (subscrut, subpat) =>
            collectPatternConds(subscrut, subpat, true)
        }
      }
      else Seq.empty
    case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
      sys.error(s"Does not know how to handle $pat")
  }

  def isLambda(c: Code): Boolean = code2sig(c).label.isLambda
  def isLambdaLike(c: Code): Boolean = code2sig(c).label.isLambdaLike
  def isVar(c: Code): Boolean = code2sig(c).label.isVar

  /*
  // TODO: Dire que dans le graphe, cela equivaut a update les references selon repl.
  //  En particulier on ne duplique pas ("freshen locals") les let, lambda, forall, choose, etc.!!!
  def replaceIn(c: Code, repl: Map[Code, Code]): Code = {
    assert(repl.forall { case (old, nw) => codeTpe(old) == codeTpe(nw) })
    repl.getOrElse(c, {
      val Signature(lab, children) = code2sig(c)
      val replChildren = children.map(replaceIn(_, repl))
      val newSig = Signature(lab, replChildren)
      codeOfSig(newSig, codeTpe(c))
    })
  }

  def replaceIn(pat: LabelledPattern, repl: Map[Code, Code]): LabelledPattern = {
    ???
//    val newScrut = replaceIn(pat.scrut, repl)
//    pat match {
//      case LabelledPattern.Wildcard(_) => LabelledPattern.Wildcard(newScrut)
//      case LabelledPattern.ADT(_, id, tps, subps) =>
//        LabelledPattern.ADT(newScrut, id, tps, subps.map(replaceIn(_, repl)))
//      case LabelledPattern.TuplePattern(_, subps) =>
//        LabelledPattern.TuplePattern(newScrut, subps.map(replaceIn(_, repl)))
//      case LabelledPattern.Lit(_, lit) => LabelledPattern.Lit(newScrut, lit)
//      case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
//        sys.error(s"Does not know how to handle $pat")
//    }
  }
  */

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def codeOfVarId(v: VarId): Code = codeOfSig(mkVar(v), varTpe(v))

  def codeOfLit[T](l: Literal[T]): Code = codeOfSig(mkLit(l), l.getType)

  private val codePurityInst = new CodePurity

  def codePurity(c: Code)(using env: OEnv, ctxs: Ctxs): Purity = codePurityInst.codePurity(c)(using env.copy(forceBinding = true))

  // TODO: Quid simplification au sein des ctx????
  // TODO: Quid simplification au sein des ctx????
  // TODO: Quid simplification au sein des ctx????
  // TODO: Quid simplification au sein des ctx????
  // TODO: Quid simplification au sein des ctx????
  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  def simplifyTopLvl(cr: CodeRes, lb: LetBind)(using OEnv): CodeRes = {
    given ctxs: Ctxs = cr.ctxs
    val tpe = codeTpe(cr.terminal)
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)

    code2sig(cr.terminal) match {
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Let(_), _) =>
        sys.error("Quoi????")

      // TODO: A gérer
      /*
      case Signature(Label.Ensuring, Seq(body, pred)) =>
        code2sig(pred) match {
          case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => cr.derived(body)
          case _ => cr
        }
      */

      case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
        val pCond = codePurity(cond)
        lazy val pThen = codePurity(thenn)
        lazy val pEls = codePurity(els)
        // TODO: On peut faire des trucs comme ifExpr
        val fstTry: Option[CodeRes] = {
          if (pCond.isPure) {
            def checkBranch(branch: CodeRes): CodeRes = {
              val (prevCtxs, ifCtx) = cr.ctxs.popOrId
              assert(prevCtxs.isPrefixOf(branch.ctxs))
              assert(ifCtx match {
                case Ctx.BoundDef(_, term, _) => term == cr.terminal
                case _ => false
              }, s"Trahison! Trahison! On a $ifCtx !!!")
              // TODO: On ne prend *pas* Usages de unplug, n'est-ce pas?
              // TODO: Usages ok? On ne compte pas cond car est true ou false
              branch
            }
            if ((cond == trueCode && pEls.isPure) || thenn == els) Some(checkBranch(unplugged(thenn).get._1))
            else if (cond == falseCode && pThen.isPure) Some(checkBranch(unplugged(els).get._1))
            else None
          } else None
        }
        def sndTry: CodeRes = (code2sig(thenn), code2sig(els)) match {
          // TODO: A revisiter une fois que l'on a ces conjuncts, etc.
          /*
          case (Signature(Label.IfExpr, Seq(cond2, thenn2, elze2)), _) if elze == elze2 =>
            val combinedCond = conjunct(Seq(cond, cond2))
            val c2 = codeOfSig(mkIfExpr(combinedCond, thenn2, elze2), tpe)
            val c3 = withIncreasedDepth(1)(transform(c2, repl, ()))
            code2sig(c3)
          case (_, Signature(Label.IfExpr, Seq(cond2, thenn2, elze2))) if thenn == thenn2 =>
            val combinedCond = simplifiedDisjunction(Seq(cond, cond2))
            val c2 = codeOfSig(mkIfExpr(combinedCond, thenn2, elze2), tpe)
            val c3 = withIncreasedDepth(1)(transform(c2, repl, ()))
            code2sig(c3)
          */
          case _ => cr
        }
        fstTry.getOrElse(sndTry)

      case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
        isConstructor(e, adt, id) match {
          case Some(b) => cr.derivedFromCtxs(b2c(b))
          case None => cr
        }

      case Signature(Label.ADTSelector(_, ctor, sel), Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.ADT(id, _), args) =>
            assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
            val index = ctor.definition.selectorID2Index(sel)
            cr.derivedFromCtxs(args(index))
          case _ => cr
        }

      case Signature(Label.ADT(id, tps), args) =>
        // Simplification de ADT(base.fld1, base.fld2, etc.) en base si base est de meme nature que l'adt construite
        val ctor: TypedADTConstructor = getConstructor(id, tps)
        assert(ctor.fields.size == args.size)

        def sameBase(i: Int, baseSoFar: Option[Code]): Option[Code] = {
          if (i == args.size) baseSoFar
          else {
            val fldId: Identifier = ctor.fields(i).id
            code2sig(args(i)) match {
              // TODO: Orig fait e.getType == adt.getType, mais nous on fait ctor == ctor2, est-ce que ça va aussi?
              case Signature(Label.ADTSelector(_, ctor2, sel), Seq(base))
                if fldId == sel && ctor == ctor2 &&
                  baseSoFar.forall(_ == base) &&
                  isConstructor(base, ADTType(id, tps), id) == Some(true) =>
                sameBase(i + 1, Some(base))
              case _ => None // L'aventure se termine ici
            }
          }
        }

        sameBase(0, None) match {
          case Some(base) =>
            cr.derivedFromCtxs(base)
          case None => cr
        }

      case Signature(Label.TupleSelect(ii), Seq(e)) =>
        val i = ii - 1
        code2sig(e) match {
          case Signature(Label.Tuple, args) => cr.derivedFromCtxs(args(i))
          case _ => cr
        }

//      case Signature(Label.Application, callee +: args) =>
//        code2sig(callee) match {
//          case Signature(Label.Lambda(params), Seq(body)) =>
//            assert(args.size == params.size)
//            val bodyUnpl = unplugged(body).get._1
//            assert(cr.ctxs.isPrefixOf(bodyUnpl.ctxs))
//            inlineLambda(cr.ctxs, params.zip(args), body, lb)
//          case _ => cr
//        }

      case Signature(Label.Not, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.Not, Seq(e2)) => cr.derivedFromCtxs(e2)
          case _ => cr
        }

      case Signature(lab@(Label.Equals | Label.GreaterEquals | Label.LessEquals | Label.LessThan | Label.GreaterThan), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Equals | Label.GreaterEquals | Label.LessEquals => trueCode
          case Label.LessThan | Label.GreaterThan => falseCode
        }
        if (e1 == e2) cr.derivedFromCtxs(resIfEq)
        else cr

      case Signature(Label.UMinus, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.UMinus, Seq(e2)) => cr.derivedFromCtxs(e2)
          case _ => cr
        }

      case Signature(Label.Plus, Seq(e1, e2)) =>
        if (e1 == zero) cr.derivedFromCtxs(e2)
        else if (e2 == zero) cr.derivedFromCtxs(e1)
        else cr

      case Signature(Label.Minus, Seq(e1, e2)) =>
        if (e1 == e2) cr.derivedFromCtxs(zero)
        else cr

      case Signature(Label.Times, Seq(e1, e2)) =>
        if (e1 == zero || e2 == zero) cr.derivedFromCtxs(zero)
        else if (e1 == one) cr.derivedFromCtxs(e2)
        else if (e2 == one) cr.derivedFromCtxs(e1)
        else cr

      case Signature(lab@(Label.Division | Label.Remainder | Label.Modulo), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Division => one
          case Label.Remainder | Label.Modulo => zero
        }
        if (opts.assumeChecked && e2 != zero && e1 == zero) cr.derivedFromCtxs(zero)
        else if (opts.assumeChecked && e2 != zero && e1 == e2) cr.derivedFromCtxs(resIfEq)
        else cr

      case Signature(Label.BVNot, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.BVNot, Seq(e2)) => cr.derivedFromCtxs(e2)
          case _ => cr
        }

      case Signature(Label.BVAnd, Seq(e1, e2)) =>
        if (e1 == e2) cr.derivedFromCtxs(e1)
        else if (e1 == zero || e2 == zero) cr.derivedFromCtxs(zero)
        else cr

      case Signature(Label.BVOr, Seq(e1, e2)) =>
        if (e1 == e2) cr.derivedFromCtxs(e1)
        else if (e1 == zero) cr.derivedFromCtxs(e2)
        else if (e2 == zero) cr.derivedFromCtxs(e1)
        else cr

      case Signature(Label.BVXor, Seq(e1, e2)) =>
        if (e1 == e2) cr.derivedFromCtxs(zero)
        else if (e1 == zero) cr.derivedFromCtxs(e2)
        else if (e2 == zero) cr.derivedFromCtxs(e1)
        else cr

      case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
        if (e2 == zero) cr.derivedFromCtxs(e1) else cr

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val cases = pats.zip(guards).zip(rhss).map {
          case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
        }
        simplifyCases(scrut, cases) match {
          case SimplifiedCases.Empty => sys.error("ah bah là, je sais pas quoi faire...")
          case SimplifiedCases.ElidableMatchExpr(rhs) =>
            // TODO: Ok???
            val (prevCtxs, matchCtx) = cr.ctxs.popOrId
            assert(matchCtx match {
              case Ctx.BoundDef(_, term, _) => term == cr.terminal
              case _ => false
            }, s"Trahison! Trahison! On a $matchCtx !!!")
            val rhsUnpl = unplugged(rhs).get._1
            assert(prevCtxs.isPrefixOf(rhsUnpl.ctxs))
            rhsUnpl

          case SimplifiedCases.Cases(newCases) =>
//            val newMatch = codeOfSig(mkMatchExpr(scrut, newCases), tpe)
            // TODO: Se débrouiller pour retrouver comp. de newCases
            // TODO: Se débrouiller pour retrouver comp. de newCases
            // TODO: Se débrouiller pour retrouver comp. de newCases
            cr //.derived(newMatch)
        }

      // TODO: Or not etc.

      case _ => cr
    }
  }

  enum SimplifiedCase {
    case Unreachable
    case Covered
    case Unchanged(caseConds: Seq[Code])
  }

  enum SimplifiedCases {
    case Empty
    case ElidableMatchExpr(rhs: Code)
    case Cases(res: Seq[LabMatchCase])
  }

  def simplifyCase(scrut: Code, matchCase: LabMatchCase)(using env: OEnv, ctxs: Ctxs): SimplifiedCase = {
    val patConds = collectPatternConds(scrut, matchCase.pattern, recursive = true)
    val caseConds = patConds :+ matchCase.guard
    lazy val isRhsPure = codePurity(matchCase.rhs)(using env, ctxs.withConds(caseConds)).isPure

    if (caseConds.forall(c => codePurity(c).isPure)) { // TODO: Calcul de la pureté imprécis, on devrait les accumuler...
      val caseCondsConj = conjunct(caseConds, mayDrop = true, mayReorder = true) // Puisque tout est pur
      if (caseCondsConj == trueCode) SimplifiedCase.Covered
      else if (caseCondsConj == falseCode && isRhsPure) SimplifiedCase.Unreachable
      else SimplifiedCase.Unchanged(caseConds)
    } else SimplifiedCase.Unchanged(caseConds)
  }

  def simplifyCases(scrut: Code, cases: Seq[LabMatchCase])(using OEnv, Ctxs): SimplifiedCases = {
    def rec(cases: Seq[LabMatchCase], acc: Seq[LabMatchCase])(using ctxs: Ctxs): SimplifiedCases = {
      if (cases.isEmpty) {
        if (acc.isEmpty) SimplifiedCases.Empty
        else SimplifiedCases.Cases(acc)
      } else simplifyCase(scrut, cases.head) match {
        case SimplifiedCase.Unreachable => rec(cases.tail, acc)
        case SimplifiedCase.Covered =>
          if (acc.isEmpty) SimplifiedCases.ElidableMatchExpr(cases.head.rhs)
          else {
            val wildcard = LabMatchCase(LabelledPattern.Wildcard(cases.head.pattern.bdg), cases.head.guard, cases.head.rhs)
            SimplifiedCases.Cases(acc :+ wildcard)
          }
        case SimplifiedCase.Unchanged(caseConds) =>
          val negCaseConds = negatedConjunction(caseConds)
          rec(cases.tail, acc :+ cases.head)(using ctxs.withCond(negCaseConds))
      }
    }
    rec(cases, Seq.empty)
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  def inlineLetBoundLambda(lam: VarId, cLam: Code, in: Code)(using env: OEnv, ctxs: Ctxs): CodeRes = {
    val lamVarIdCode = codeOfVarId(lam)
    val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam)

    class InlineWrapperImpl extends CodeTransformer {
      override type Extra = Unit

      // TODO: Ok par rapport à repl + let-bound canSubst truc?
      override def transformImpl(c: Code, lb: LetBind, repl: Map[Code, Code], extra: Unit)
                                (using env: OEnv, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(Label.Var(`lam`), Seq()) =>
//          CodeRes.lambdaLike(Label.Lambda(params), unplugged(body).get._1, lb)
          CodeRes.of(cLam)
        case Signature(Label.Application, `lamVarIdCode` +: args) =>
          assert(params.size == args.size)
          inlineLambda(ctxs, params.zip(args), body, lb)
        case _ => super.transformImpl(c, lb, repl, ())
      }
    }

    (new InlineWrapperImpl).transform(in, Map.empty, ())
  }

  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: remarque sur subst dans l'ordre (repr. l'inlining d'argument)
  def inlineLambda(outerCtxs: Ctxs, argsSubst: Seq[(VarId, Code)], body: Code, lb: LetBind)(using env: OEnv): CodeRes = {
    given x_x: OEnv = sys.error("carefully select env")

    // Essentiellement un freshener + simplifyTopLvl a chaque step
    class InlinerImpl extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, lb: LetBind, repl: Map[Code, Code], extra: Unit)(using env: OEnv, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(Label.Let(v), Seq(e, b)) =>
          val freshV = freshened(v)
          // CodeTransformer va se charger de faire la substitution
          val newLet = codeOfSig(mkLet(freshV, e, b), lb.tpe)
          val rec = super.transformImpl(newLet, lb, repl + (codeOfVarId(v) -> codeOfVarId(freshV)), ())
          simplifyTopLvl(rec, lb)

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val freshParams = lab.params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
          val newLab = lab.replacedParams(freshParams.map(_._2))
          val newLam = codeOfSig(mkLambdaLike(newLab, body), lb.tpe)
          val rec = super.transformImpl(newLam, lb, repl ++ freshParamsRepl, ())
          simplifyTopLvl(rec, lb)

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          assert(2 * pats.size == guardRhs.size)
          // TODO: Ok????
          // TODO: Ok????
          // TODO: Ok????
          // TODO: Ok????
          // TODO: A tester!!!!
          // TODO: A tester!!!!
          // TODO: A tester!!!!
          // TODO: A tester!!!!
          val (newPats, freshBdgs) = pats.map(pat => pat.bdg match {
            case Some(bdg) =>
              val freshBdg = freshened(bdg)
              (pat.withBinding(Some(freshBdg)), Some(codeOfVarId(bdg) -> codeOfVarId(freshBdg)))
            case None => (pat, None)
          }).unzip
          val newMatch = codeOfSig(Signature(Label.MatchExpr(newPats), scrut +: guardRhs), lb.tpe)
          val rec = super.transformImpl(newMatch, lb, repl ++ freshBdgs.flatten.toMap, ())
          simplifyTopLvl(rec, lb)

        case Signature(_, _) =>
          val rec = super.transformImpl(c, lb, repl, ())
          simplifyTopLvl(rec, lb)
      }
    }

    // TODO: Remarque: inline une lambda peut donner lieu a une expr impure...
    val bodyTpe = codeTpe(body)
    val freshVars = argsSubst.map { case (v, _) => v -> freshened(v) }
    val freshVarsMap = freshVars.toMap

    val (initEnv, initCtxs) = argsSubst.foldLeft((env, outerCtxs)) {
      case ((env, ctxs), (oldV, arg)) =>
        given OEnv = env
        given Ctxs = ctxs
        code2sig(arg).label match {
          case Label.Var(argVar) =>
            assert(!env.varSubst.contains(argVar))
            (env.addVarSubst(oldV, argVar), ctxs)
          case Label.Lit(l) =>
            (env.addLitSubst(oldV, l), ctxs)
          case _ =>
            val newV = freshVarsMap(oldV)
            // TODO: Il faudra s'assurer que les oldV se font subst par newV qui se font subst par arg
            // TODO: Comp ok???
            (env.addVarSubst(oldV, newV), ctxs.addBoundDef(newV, arg, Occurrences.of(arg)))
        }
    }

    // Map to replace all occurrences of the old parameter with the fresh bindings variables.
    val initRepl = freshVars.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
    val inlined = (new InlinerImpl).transform(body, lb, initRepl, ())(using initEnv, initCtxs)
    assert(codeTpe(inlined.terminal) == bodyTpe)
    inlined

//    // Bind the argument to fresh variables
//    val envsBdgs = freshVars.map {
//      case (oldV, newV) => newV -> argsSubstMap(oldV)
//    }
//
//    // TODO: Env par defaut et pas celui du body?
//    val (initEnv, bdgsCtx) = envsBdgs.foldLeft((env, Ctxs.empty)) {
//      case ((env, ctxsAcc), (v, arg)) =>
//        given OEnv = env
//        val isLam = isLambda(arg)
//        // TODO: Usages ok???
//        val ctx = Ctx.BoundDef(v, arg, isLam, Occurrences.of(arg), env, !isLam)
//        (env.withLetBound(v, arg, !isLam), ctxsAcc :+ ctx)
//    }
//    // Map to replace all occurrences of the old parameter with the fresh bindings variables.
//    val initRepl = freshVars.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
//    val inlined = (new InlinerImpl).transform(body.terminal, initRepl, ())(using initEnv)
//    assert(codeTpe(inlined.terminal) == bodyTpe)
//    // TODO: Quel ctxs rajouter???
//    // TODO: Usages ok?
//    CodeRes(inlined.terminal, inlined.terminalHasLambdaDef, outerCtxs ++ bdgsCtx ++ inlined.ctxs, inlined.usages, inlined.env)
  }

  // TODO: Nom de fn: aussi selon env.varSubst...
  def substByLet(v: VarId)(using env: OEnv, ctxs: Ctxs): Option[Code] = {
    env.varSubst.get(v) match {
      case Some(c) => code2sig(c).label match {
        case Label.Var(v2) =>
          // Pas d'alias d'alias etc.
          assert(!env.varSubst.contains(v2))
          ctxs.boundTo(v2).filterNot(isLambda).orElse(Some(c))

        case lab =>
          assert(lab.isLiteral)
          Some(c)
      }
      case None => ctxs.boundTo(v).filterNot(isLambda)
    }
  }

  class CodePurity extends CodeTryFolder[Unit, Purity] {
    override type Extra = Unit

    private val visiting = mutable.Set.empty[Code]

    def codePurity(c: Code)(using OEnv, Ctxs): Purity = tryFold(c, Pure, ()).getOrElse(Impure)

    override def tryFoldImpl(c: Code, acc: Purity, extra: Unit)(using env: OEnv, ctxs: Ctxs): Either[Unit, Purity] = {
      if (acc == Impure) Left(())
      else if (ctxs.isBoundDef(c)) Right(acc)
      else {
        if (visiting(c)) {
          println(s"!!! Already visited $c  =  ${code2sig(c)}")
        }
        visiting += c
        val purityC = code2sig(c) match {
          case Signature(Label.Var(v), Seq()) =>
            assert(!env.varSubst.contains(v))
            Pure
          case Signature(Label.Lit(_), Seq()) => Pure
          case Signature(Label.Assume, Seq(pred, body)) =>
            if (pred == trueCode) codePurity(body) // pas besoin de ctxs.withCond car de toute façon c'est true
            else Impure

          case Signature(Label.Assert | Label.Require, Seq(pred, body)) =>
            val pBody = codePurity(body)(using env, ctxs.withCond(pred))
            if (pred == trueCode) pBody
            else assmChkPurity ++ pBody // Pureté comme Stainless

          case Signature(Label.Ensuring, Seq(body, pred)) =>
            code2sig(pred) match {
              case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => codePurity(body)
              case _ => Impure
            }

          case Signature(Label.ADTSelector(adt, ctor, _), Seq(e)) =>
            if (opts.assumeChecked || isConstructor(e, adt, ctor.id) == Some(true)) codePurity(e)
            else Impure

          case Signature(Label.ADT(id, tps), args) =>
            // TODO: Ok? Il y a un commentaire dans SWP...
            val ctor: TypedADTConstructor = getConstructor(id, tps)
            val consingPurity = {
              if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
              else Impure
            }
            consingPurity ++ fold(args.map(codePurity))

          case Signature(Label.Lambda(_), Seq(_)) => Pure

          case Signature(Label.FunctionInvocation(id, _), args) =>
            fold(args.map(codePurity)) ++ fnPurity(id)

          case Signature(Label.Application, callee +: args) =>
            // TODO: Dans SWP: quid pureté callee???
            // TODO: Pureté ok? Après tout, un inline de lambda peut donner lieu à impure...
            assmChkPurity ++ codePurity(callee) ++ fold(args.map(codePurity))

          case Signature(Label.Choose(v), Seq(pred)) =>
            if (pred == trueCode && hasInstance(varTpe(v)) == Some(true)) Pure
            else Impure

          // TODO: Pureté ok pour NoTree/Error? Car dans SWP et isImpure, aucune mention de NoTree/Error...
          case Signature(Label.Division | Label.Remainder | Label.Modulo | Label.NoTree(_) | Label.Error(_, _), _) =>
            assmChkPurity // TODO: Ok?

          // TODO: Pureté de Decreases?
          // TODO: Array select, map select, etc.???

          case _ => super.tryFoldImpl(c, Pure, ()).getOrElse(Impure)
        }

        val purity = acc ++ purityC
        // TODO: Temporaire
        // TODO: Est-ce ok???
        purity match {
          case Pure | Impure => ()
          case Delayed(blockers) =>
            codeBlockedBy += c -> blockers
            for (blocker <- blockers) {
              // TODO: les blocking, codeBlockedBy et toussa devrait aller dans cette class SigPurity
              val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
              blocking += blocker -> (blockedFns, blockedCodes + c)
            }
        }
        visiting -= c
        if (purity == Impure) Left(()) else Right(purity)
      }
    }
  }

  private val codeOcc = new CodeOccurrences
  def occurrencesOf(c: Code)(using env: OEnv, ctxs: Ctxs): Occurrences =
    codeOcc.tryFold(c, Occurrences.empty, ()).getOrElse(sys.error("impossible"))

    // TODO: Cette histoire de acc... ça à l'air faux!!!
  class CodeOccurrences extends CodeTryFolder[Unit, Occurrences] {
    override type Extra = Unit

    // TODO: C'est faux: c'est slmt par rapport aux children!
    // TODO: C'est faux: c'est slmt par rapport aux children!
    // TODO: C'est faux: c'est slmt par rapport aux children!
    override def tryFoldImpl(c: Code, acc: Occurrences, extra: Unit)(using env: OEnv, ctxs: Ctxs): Either[Unit, Occurrences] = {
      code2sig(c).label match {
        case Label.Lit(_) =>
          return Right(acc)
        case Label.Var(v) =>
          assert(!env.varSubst.contains(v))
          return Right(acc ++ Occurrences.of(c)) // TODO: Non, la composition d'une var, c'est empty
        case _ => ()
      }
      if (ctxs.isBoundDef(c)) Right(acc ++ Occurrences.of(c))
      else {
        code2sig(c) match {
          case Signature(Label.Let(v), Seq(e, b)) =>
            val occE = occurrencesOf(e)
            val occB = occurrencesOf(b)(using env, ctxs.addBoundDef(v, e, occE))
            val defnCode = if (isLambda(e)) codeOfVarId(v) else e
            // TODO: Ou devrait aller acc?
            Right(occE ++ (acc ++ occB).setTo(defnCode, Occurrence.Once(ctxs, env.inLambda)))

          case _ =>
            // TODO: Match? Assume?
            super.tryFoldImpl(c, acc, ())
        }
      }
    }
  }

  // TODO: Commentaire à propos de code potentiel dans les labels qui ne sont pas transform
  class CodeTransformer {
    type Extra

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using env: OEnv, ctxs: Ctxs): CodeRes =
      transform(c, LetBind.empty(codeTpe(c)), repl, extra)

    final def transform(c: Code, lb: LetBind, repl: Map[Code, Code], extra: Extra)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(codeTpe(c) == lb.tpe)
      val res = repl.get(c) match {
        case Some(cc) =>
          // assert(env.isBound(cc), "repl fait référence à un code qui n'est pas let-bound!!!") // TODO: Et alors?
          // Si cc est une var à un enclosing let, on le remplace par sa définition (pr autant que cela est permis)
          val res = code2sig(cc) match {
            case Signature(Label.Var(v), Seq()) => substByLet(v).getOrElse(cc)
            case _ => cc
          }
          CodeRes.of(res)
        case None =>
          transformImpl(c, lb, repl, extra)
      }
      assert(ctxs.isPrefixOf(res.ctxs))
      res
    }

    def transformImpl(c: Code, lb: LetBind, repl: Map[Code, Code], extra: Extra)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(codeTpe(c) == lb.tpe)
      assert(!repl.contains(c), s"$c = ${code2sig(c)} n'a pas été remplacé par transform")

      code2sig(c) match {
        case Signature(Label.Var(v), Seq()) =>
          // Comme repl ne peut contenir v, on utilise substByLet
          val res = substByLet(v).getOrElse(codeOfVarId(v))
          CodeRes.of(res)

        case Signature(Label.Let(v), Seq(e, b)) =>
          val re = transform(e, LetBind.of(v), repl, extra)
          // TODO: OK par rapport au var, lit etc.?
          // TODO: Remarque: pas besoin de modifier env.varSubst car subsumed par repl, qui est plus général
          transform(b, lb, repl + (e -> re.terminal), extra)(using env, re.ctxs.addBoundDef(v, re.terminal, re.terminalComposition))

        case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
          val rcond = transform(cond, repl, extra)
          val thennCtxs = rcond.ctxs.withCond(rcond.terminal)
          val rthenn = transform(thenn, repl, extra)(using env, thennCtxs)
          val elsCtxs = rcond.ctxs.withCond(negCodeOf(rcond.terminal)) // (using rcond.env)
          val rels = transform(els, repl, extra)(using env, elsCtxs)
          CodeRes.ifExpr(rcond, rthenn, rels, lb)

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val rbody = transform(body, repl, extra)(using env.copy(inLambda = env.inLambda || lab.isLambda))
          CodeRes.lambdaLike(lab, rbody, lb)

        case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
          val rpred = transform(pred, repl, extra)
          transform(body, lb, repl, extra)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal, rpred.terminalComposition))

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          // TODO: Ok?
          val rbody = transform(body, repl, extra)
          val rpred = transform(pred, repl, extra)
          CodeRes.ensuring(rbody, rpred, lb.tpe)

        case Signature(Label.Or, disjs) =>
          // TODO: copié collé adapté de codeOfDisjunction...
          val outerCtxs = ctxs
          val (_, composition, rdisjs) = unOrCodes(disjs).foldLeft((outerCtxs, Occurrences.empty, Seq.empty[Code])) {
            case ((ctxs, compAcc, rdisjsAcc), disj) =>
              assert(outerCtxs.isPrefixOf(ctxs))
              assert(outerCtxs.bindings == ctxs.bindings)

              given Ctxs = ctxs
              val rdisj = transform(disj, repl, extra)
              // Remarque: c'est bien le ctxs d'origine qu'on utilise,
              // pas celui de re car celui-ci contient des bdgs et d'autres conds (qui ne sont pas carry over)
              val (occ, rdisjPlugged) = rdisj.selfPlugged(outerCtxs)
              // Ditto ici
              val newCtxs = outerCtxs.withCond(negCodeOf(rdisjPlugged))
              (newCtxs, compAcc ++ occ, rdisjsAcc :+ rdisjPlugged)
          }
          val isPure = rdisjs.forall(c => codePurity(c).isPure)
          val ror = simplifiedDisjunction(rdisjs, mayDrop = isPure, mayReorder = isPure) // rooooaaaaarr... ah non c'est pas ça...
          unplugged(ror) match {
            case Some((cr, _)) => cr // TODO: Mais c'est dégueulasse !!!! Et c'est quoi la justification au juste?????
            case None =>
              // Remarque: on retourne le ctx original car les PCs des ors ne sont pas retenues hors des disjunctions.
              // P.ex. dans val x = b1 || b2 || b3 il serait insensé d'avoir !b1 && !b2 && !b3 dans le env de x.
              val bdg = lb.getOrFresh("orBdg")
              // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
              // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
              // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
              // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
              // TODO: Et la composition alors??? Si tout est simplifié, il faudrait retourner Occ.empty non???
              val actualComp = composition
              CodeRes(ror, actualComp, outerCtxs.addBoundDef(bdg, ror, actualComp))
          }

        // TODO: Quid lb???
        case sig@Signature(Label.Lit(_) | Label.Error(_, _) | Label.NoTree(_), Seq()) =>
          CodeRes.of(codeOfSig(sig, lb.tpe))

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          assert(2 * pats.size == guardRhs.size)
          val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
          val cases = pats.zip(guards).zip(rhss).map {
            case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
          }
          val rscrut = transform(scrut, repl, extra)
          val rcases = transformCases(scrut, rscrut.terminal, cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using env, rscrut.ctxs)
          CodeRes.matchExpr(rscrut, rcases, lb)

        // TODO: Que pour les cas triviaux où env est le même, bindings std, etc.
        case Signature(lab, children) => transformSeq(children, lb, repl, extra)(Signature(lab, _))
      }
    }

    final def transformSeq(cs: Seq[Code], lb: LetBind, repl: Map[Code, Code], extra: Extra)
                          (mkSig: Seq[Code] => Signature)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      given x_x: Ctxs = sys.error("Carefully select ctxs")
      val (newCtxs, ress) = cs.foldLeft((ctxs, Seq.empty[CodeRes])) {
        case ((ctxs, codeResAcc), c) =>
          val res = transform(c, repl, extra)(using env, ctxs)
          assert(ctxs.isPrefixOf(res.ctxs))
          (res.ctxs, codeResAcc :+ res)
      }
      combineCodeRes(ress, lb)(mkSig)(using env, newCtxs)
    }

    // TODO: Ok????
    // TODO: Ok????
    // TODO: Ok????
    def transformCase(oldScrut: Code, newScrut: Code, matchCase: LabMatchCase, repl0: Map[Code, Code], extra: Extra)
                     (using env: OEnv, ctxs: Ctxs): (CodeResMatchCase, Seq[Code]) = {
      assert(repl0.get(oldScrut) == Some(newScrut), s"'repl0' ne contient pas $oldScrut -> $newScrut")
      val patConds = collectPatternConds(newScrut, matchCase.pattern, recursive = true)
      val oldBdgs = allScrutinees(oldScrut, matchCase.pattern)
      val newBdgs = allScrutinees(newScrut, matchCase.pattern)
      assert(oldBdgs.size == newBdgs.size)
      val repl = repl0 ++ oldBdgs.map(_._2).zip(newBdgs.map(_._2)).toMap
      val ctxsGuard = addScrutineeBindings(ctxs, newBdgs).withConds(patConds)
      val rguard = transform(matchCase.guard, repl, extra)(using env, ctxsGuard)
      val (compGuard, cGuard) = rguard.selfPlugged(ctxs)
      val ctxsRhs = ctxsGuard.withCond(cGuard)
      val rrhs = transform(matchCase.rhs, repl, extra)(using env, ctxsRhs)
      val (compRhs, cRhs) = rrhs.selfPlugged(ctxs)
      // TODO: Rien à transformer pour matchCase.pattern, pas vrai?
      val newMatchCase = LabMatchCase(matchCase.pattern, cGuard, cRhs)
      (CodeResMatchCase(newMatchCase, compGuard ++ compRhs), patConds :+ cGuard)
    }

    def transformCases(oldScrut: Code, newScrut: Code, cases: Seq[LabMatchCase],
                       repl: Map[Code, Code], extra: Extra,
                       acc: Seq[CodeResMatchCase])
                      (using env: OEnv, ctxs: Ctxs): Seq[CodeResMatchCase] = {
      if (cases.isEmpty) acc
      else {
        val (newMatchCase, caseConds) = transformCase(oldScrut, newScrut, cases.head, repl, extra)
        val negCaseConds = negatedConjunction(caseConds)
        transformCases(oldScrut, newScrut, cases.tail, repl, extra, acc :+ newMatchCase)(using env, ctxs.withCond(negCaseConds))
      }
    }
  }

  class CodeTryFolder[E, T] {
    type Extra

    final def tryFold(c: Code, acc: T, extra: Extra)(using env: OEnv, ctxs: Ctxs): Either[E, T] = {
      code2sig(c).label match {
        case Label.Var(v) if env.varSubst.contains(v) => tryFoldImpl(env.varSubst(v), acc, extra)
        case _ => tryFoldImpl(c, acc, extra)
      }
    }

    def tryFoldImpl(c: Code, acc: T, extra: Extra)(using env: OEnv, ctxs: Ctxs): Either[E, T] = code2sig(c) match {
      case Signature(Label.Var(v), Seq()) =>
        assert(!env.varSubst.contains(v))
        substByLet(v).map(tryFold(_, acc, extra)).getOrElse(Right(acc))

      case Signature(Label.Let(v), Seq(e, b)) =>
        for {
          re <- tryFold(e, acc, extra)
          // TODO: Pour les occurrences, comme on ne l'utilise pas, on met empty...
          rb <- tryFold(b, re, extra)(using env, ctxs.addBoundDef(v, e, Occurrences.empty))
        } yield rb

      case Signature(Label.Assert | Label.Assume | Label.Require, Seq(pred, body)) =>
        for {
          rpred <- tryFold(pred, acc, extra)
          rbody <- tryFold(body, rpred, extra)(using env, ctxs.withCond(pred))
        } yield rbody

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        for {
          rcond <- tryFold(cond, acc, extra)
          rthn <- tryFold(thn, rcond, extra)(using env, ctxs.withCond(cond))
          rels <- tryFold(els, rthn, extra)(using env, ctxs.withCond(negCodeOf(cond)))
        } yield rels

      case Signature(Label.Or, args) =>
        tryFoldSeq(args, acc, extra) { case (disj, env) => env.withCond(negCodeOf(disj)) /*(using env)*/ }

      case Signature(Label.Lambda(_), Seq(body)) => tryFold(body, acc, extra)(using env.copy(inLambda = true), ctxs)

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val rscrut = tryFold(scrut, acc, extra)
        pats.zip(guards).zip(rhss).foldLeft(rscrut.map((_, ctxs))) {
          case (Right((acc, ctxs)), ((pat, guard), rhs)) =>
            val patConds = collectPatternConds(scrut, pat, recursive = true)
            for {
              rpat <- tryFoldSeq(patConds, acc, extra)
              rguard <- tryFold(guard, rpat, extra)(using env, ctxs.withConds(patConds))
              caseConds = patConds :+ guard
              rrhs <- tryFold(rhs, rguard, extra)(using env, ctxs.withConds(caseConds))
              negCaseConds = negatedConjunction(caseConds)
            } yield (rrhs, ctxs.withCond(negCaseConds))
          case (Left(e), _) => Left(e)
        }.map(_._1)

      // TODO: Suppose que lab pas besoin d'avoir des sous parties transformées. P.ex. pour MatchExpr, cela ne jouera pas (en raison des recs?)
      case Signature(_, children) => tryFoldSeq(children, acc, extra)
    }

    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(using OEnv, Ctxs): Either[E, T] =
      tryFoldSeq(cs, acc, extra)((_, ctxs) => ctxs)

    // TODO: Dire que le nextCtxs est appliqué pour le suivant (et pas pr le "current")
    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(nextCtxs: (Code, Ctxs) => Ctxs)(using env: OEnv, ctxs: Ctxs): Either[E, T] = {
      cs.foldLeft(Right((acc, ctxs)): Either[E, (T, Ctxs)]) {
        case (Right((acc, ctxs)), c) =>
          tryFold(c, acc, extra).map((_, nextCtxs(c, ctxs)))
        case (Left(e), _) => Left(e) // should do an early return...
      }.map(_._1)
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Map all codes to their corresponding signatures (for debugging purposes)

  case class ExplicitSig(label: Label, children: Seq[ExplicitSig]) {
    override def toString: String = {
      if (children.isEmpty) label.toString
      else s"($label, ${children.mkString(", ")})"
    }
  }

  def asExplicitSig(c: Code): ExplicitSig = {
    val sig = code2sig(c)
    ExplicitSig(sig.label, sig.children.map(asExplicitSig))
  }
}

object OCBSL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OCBSL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OCBSL
    new Impl(t, s, opts)
  }
}