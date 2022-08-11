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

  case class OEnv(inLambda: Boolean, forceBinding: Boolean)

  object OEnv {
    def empty: OEnv = OEnv(false, false)
  }

  case class InLambda(v: Boolean) {
    def ||(other: Boolean): InLambda = InLambda(v || other)
    def ||(other: InLambda): InLambda = InLambda(v || other.v)
  }

  enum Ctx {
    case Id
    case BoundDef(terminal: Code)
    case AssumeLike(lab: Label.AssumeLike, predTerminal: Code)
    case Assumed(cond: Code) // TODO: Dire que c'est p.ex. apres if (cond), où le assume(cond) ds la branche n'est pas nécessaire (car impliqué)

    lazy val hc: Int = this match {
      case Ctx.Id => 31
      case Ctx.BoundDef(t) => java.util.Objects.hash(t)
      case Ctx.AssumeLike(l, p) => java.util.Objects.hash(l, p)
      case Ctx.Assumed(c) => java.util.Objects.hash(c)
    }
    override def hashCode(): Int = hc

    def isBoundDef(c: Code): Boolean = this match {
      case Ctx.BoundDef(c2) => c == c2
      case _ => false
    }
  }

  case class Ctxs(ctxs: Seq[Ctx]) {
    assert(
      ctxs.forall {
        case Ctx.BoundDef(terminal) => !isLitOrVar(terminal)
        case _ => true
      }, "Binding de var ou lit")
    assert(
      ctxs.collect {
        case bd@Ctx.BoundDef(_) => bd
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

    lazy val bound: Seq[Code] = ctxs.collect {
      case Ctx.BoundDef(c) => c
    }


    def pop: Option[(Ctxs, Ctx)] = {
      if (ctxs.isEmpty) None
      else Some((Ctxs(ctxs.init), ctxs.last))
    }
    def popOrId: (Ctxs, Ctx) = pop.getOrElse((Ctxs(Seq.empty), Ctx.Id))

    def withRemovedBinding(c: Code): Ctxs = withRemovedBindings(Set(c))

    def withRemovedBindings(cs: Set[Code]): Ctxs = {
      Ctxs(ctxs.filterNot {
        case Ctx.BoundDef(c) => cs(c)
        case _ => false
      })
    }

    def movedAfter(after: Ctxs): Ctxs = {
      val common = this.ctxs.zip(after.ctxs).takeWhile { case (slf, after) => slf == after }.map(_._1)
      val suffixThis = this.ctxs.drop(common.size)
      val suffixAfter = after.ctxs.drop(common.size)
      val merged = common ++ suffixAfter ++ suffixThis
      Ctxs(merged)
    }

    // En gros: On plug jusqu'à ce que l'on atteigne inCtxs
    def plugged(inCtxs: Ctxs, u: Occurrences, c: Code)(using env: OEnv): (Occurrences, Code, Set[Code]) = {
      assert(inCtxs.isPrefixOf(this))

      def plugCtx(curr: Ctxs, prev: Ctxs, toPlug: Ctx, u: Occurrences, c: Code, inlinedLet: Set[Code]): (Occurrences, Code, Set[Code]) = {
        // TODO: Cette histoire de assume(...) en début de lambda????
        // TODO: Dire qu'ici et pas ailleurs car on ne veut pas remettre des ctxs.addBoundDef pr les lambdas
        def inlineAppliedLambda(cLam: Code, in: Code)(using env: OEnv, ctxs: Ctxs): CodeRes = {
          val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam)
          object inliner extends CodeTransformer {
            override type Extra = Unit
            // TODO: Test inline lambda dans lambda?
            override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)
                                      (using env: OEnv, ctxs: Ctxs): CodeRes = code2sig(c) match {
              case Signature(Label.Application, `cLam` +: args) =>
                assert(params.size == args.size)
                inlineLambda(ctxs, params.zip(args), body)
              case _ => super.transformImpl(c, repl, ())
            }
          }
          // TODO: Est-ce ok????
          // TODO: Est-ce ok????
          val res = inliner.transform(in, Map.empty, ())
          res.copy(ctxs = res.ctxs.withRemovedBindings(inlinedLet + cLam))
        }

        assert(curr.ctxs == prev.ctxs :+ toPlug)
        assert(u.allSuffixes(curr))

        val uuu0 = occurrencesOf(c)(using env, curr)
        val uuu = uuu0.withRemovedBindings(inlinedLet)
        if (u != uuu) {
          val eq = u.c2u.toSet.intersect(uuu.c2u.toSet)
          val diff = (u.c2u.toSet ++ uuu.c2u.toSet) -- eq
          assert(false, "!!! Pas d'égalité")
        }

        val (u2, c2, inlinedLet2) = toPlug match {
          case Ctx.Id | Ctx.Assumed(_) => (u, c, inlinedLet)

          case Ctx.BoundDef(terminal) =>
            assert(!isLitOrVar(terminal))
            val composition = occurrencesOf(terminal)(using env, prev) // Avec terminal
            assert(composition(terminal).isOnce)
            assert(composition.c2u.keySet.intersect(inlinedLet).isEmpty)
            val compWoTerm = composition - terminal
            val definitionOccurrence = u(terminal)
            val bdgCase = needsBinding(terminal, compWoTerm, definitionOccurrence)(using env, prev)

            if (bdgCase == BindingCase.MustBind) {
              val cLet = codeOfSig(mkLet(terminal, c), codeTpe(c))
              // TODO: pr le setTo: y-a-t-il tjrs un sens à cela? parce que de toute façon, on est sensé bind "tout en haut" non?
              // TODO: inCtx: avec ou sans le binding?
              // TODO: defn ou terminal? Hmm, ce serait plutot terminal, meme pr lambda non?
              val u2 = compWoTerm ++ u.setTo(terminal, Occurrence.Once(prev, env.inLambda)) // TODO: Hmm est-ce "vrai"?
              (u2, cLet, inlinedLet)
            } else if (bdgCase == BindingCase.Inlinable && isLambda(terminal)) {
              val res = inlineAppliedLambda(terminal, c)(using env, prev)
              assert(prev.isPrefixOf(res.ctxs))
              val (u2, c2) = res.selfPlugged(prev)
              // TODO: Dire pk: en gros parce que ce bdg est removed
              // TODO: Dire pk on re-remove les inlinedLet: car res.selfPlugged va revisiter c
              val u3 = u2.withRemovedBindings(inlinedLet + terminal)
              (u3, c2, inlinedLet + terminal)
            } else {
              val u2 = definitionOccurrence match {
                case Occurrence.Zero => u
                case Occurrence.Once(inCtxs, inLambda) =>
                  u ++ compWoTerm.withInlinedOccurrences(inCtxs.withRemovedBinding(terminal), inLambda)
                case Occurrence.Many => sys.error("cannot happen (would have fallen under 'MustBind' case)")
              }
              // TODO: Dire pk: en gros parce que ce bdg est removed
              val u3 = u2.withRemovedBinding(terminal)
              (u3, c, inlinedLet + terminal)
            }

          case Ctx.AssumeLike(lab, predTerminal) =>
            assert(prev.isLitVarOrBoundDef(predTerminal))
            val c2 = codeOfSig(mkAssumeLike(lab, predTerminal, c), codeTpe(c))
            (u ++ Occurrences.of(predTerminal)(using env, prev), c2, inlinedLet)
        }

        assert(u2.allSuffixes(prev))

        val uuu20 = occurrencesOf(c2)(using env, prev)
        val uuu2 = uuu20.withRemovedBindings(inlinedLet2)
        if (u2 != uuu2) {
          val eq = u2.c2u.toSet.intersect(uuu2.c2u.toSet)
          val diff = (u2.c2u.toSet ++ uuu2.c2u.toSet) -- eq
          assert(false, "!!! Pas d'égalité2")
        }

        (u2, c2, inlinedLet2)
      }


      def rec(curr: Ctxs, u: Occurrences, c: Code, inlinedLet: Set[Code]): (Occurrences, Code, Set[Code]) = {
        assert(inCtxs.isPrefixOf(curr))
        assert(curr.isPrefixOf(this))
        if (curr.ctxs.size == inCtxs.ctxs.size) (u, c, inlinedLet)
        else {
          assert(curr.ctxs.nonEmpty)
          val (prev, toPlug) = curr.popOrId
          val (u2, c2, inlinedLet2) = plugCtx(curr, prev, toPlug, u, c, inlinedLet)
          rec(prev, u2, c2, inlinedLet2)
        }
      }

      rec(this, u, c, Set.empty)
    }

    def isBoundDef(c: Code): Boolean = ctxs.exists(_.isBoundDef(c))

    def isLitVarOrBoundDef(c: Code): Boolean = isLitOrVar(c) || isBoundDef(c)

    def isPrefixOf(that: Ctxs): Boolean = ocbsl.isPrefixOf(this.ctxs, that.ctxs)

    def addBoundDef(df: Code): Ctxs = {
      if (isLitOrVar(df) || isBoundDef(df)) this
      else Ctxs(ctxs :+ Ctx.BoundDef(df))
    }

    def withCond(cond: Code): Ctxs = {
      // TODO: Bind si nécessaire (voir autre branche)
      // assert(isLitOrVar(cond) || isBoundDef(cond)) // TODO: Non, c'est que pr les Or, if branch etc.
      if (cond == trueCode || allCondsSet.contains(cond)) this
      else Ctxs(ctxs :+ Ctx.Assumed(cond))
    }

    def withConds(conds: Seq[Code]): Ctxs = {
      // TODO: Bind si nécessaire (voir autre branche)
      // assert(conds.forall(c => isLitOrVar(c) || isBoundDef(c))) // TODO: Non, c'est que pr les Or, if branch etc.
      val toAdd = conds.distinct.filterNot(allCondsSet)
      if (toAdd.isEmpty) this
      else Ctxs(ctxs ++ toAdd.map(Ctx.Assumed.apply))
    }

    def withAssumeLike(kind: Label.AssumeLike, pred: Code): Ctxs = {
      assert(isLitVarOrBoundDef(pred))
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

    def -(c: Code): Occurrences = Occurrences(c2u - c)

    // TODO: What is this name!!!!
    def manyied: Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Zero) => (c, Occurrence.Zero) // TODO: Should we just filter these out?
      case (c, _) => c -> Occurrence.Many
    })

    def allSuffixes(ctxs: Ctxs): Boolean = c2u.values.forall {
      case Occurrence.Once(inCtxs, _) => ctxs.isPrefixOf(inCtxs)
      case _ => true
    }

    def withInlinedOccurrences(newInCtxs: Ctxs, inLambda: Boolean): Occurrences = {
      Occurrences(c2u.map {
        case (c, Occurrence.Once(prevInCtxs, inLambda2)) =>
          val ctxs = prevInCtxs.movedAfter(newInCtxs)
          c -> Occurrence.Once(ctxs, inLambda || inLambda2)
        case (c, occ) => c -> occ
      })
    }

    def withRemovedBinding(bound: Code): Occurrences = withRemovedBindings(Set(bound))

    def withRemovedBindings(bound: Set[Code]): Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Once(inCtxs, inLambda)) =>
        c -> Occurrence.Once(inCtxs.withRemovedBindings(bound), inLambda)
      case (c, occ) => c -> occ
    })
  }

  object Occurrences {
    def empty: Occurrences = Occurrences(Map.empty)

    def of(c: Code)(using env: OEnv, ctxs: Ctxs): Occurrences = {
      if (code2sig(c).label.isLiteral) Occurrences.empty
      else Occurrences(Map(c -> Occurrence.Once(ctxs, env.inLambda)))
    }
  }

  case class LetValSubst(subst: Map[Variable, Code]) {
    def apply(v: Variable): Code = {
      assert(subst.contains(v))
      subst(v)
    }

    def get(v: Variable): Option[Code] = subst.get(v)

    def +(t: (Variable, Code)): LetValSubst = {
      assert(!subst.contains(t._1))
      LetValSubst(subst + t)
    }
  }
  object LetValSubst {
    def empty: LetValSubst = LetValSubst(Map.empty)
  }

  private val pluggedMap = mutable.Map.empty[(CodeRes, Ctxs, OEnv), (Occurrences, Code)]
  private val unplugMap = mutable.Map.empty[(Code, OEnv), (CodeRes, Occurrences, Ctxs)]

  def unplugged(c: Code)(using env: OEnv): Option[(CodeRes, Occurrences, Ctxs)] = unplugMap.get((c, env))

  case class CodeRes(terminal: Code, ctxs: Ctxs) {
    assert(CodeRes.isTerminal(terminal), s"Gag: $terminal n'est pas un terminal (est un ${code2sig(terminal)})")
    // assert(!isLambda(terminal)) // TODO: Non, car comment pourrait on repr. un lambda sans bdg? (= eta expand/inlined)
    // assert(terminalComposition(terminal).isZero, s"Gag: $terminal (${code2sig(terminal)}) apparait dans $terminalComposition !!!") // TODO: Bah non...

    lazy val hc: Int = java.util.Objects.hash(terminal, ctxs)
    override def hashCode(): Int = hc

    def selfPlugged(inCtxs: Ctxs)(using env: OEnv): (Occurrences, Code) = {
/*
      if (isLitOrVar(terminal)) {
        // TODO: Which ctxs?
        return (Occurrences.of(terminal)(using env, ctxs), terminal)
      } else if (code2sig(terminal).label.isEnsuring) {
        assert(ctxs.ctxs.isEmpty)
        assert(inCtxs.ctxs.isEmpty)
        return (occurrencesOf(terminal)(using env, ctxs), terminal)
      }
*/
      pluggedMap.getOrElseUpdate((this, inCtxs, env), {
        assert(inCtxs.isPrefixOf(ctxs))
//        val u = Occurrences.of(terminal)(using env, ctxs) // TODO: Pas tout à fait en raison de ensuring. p-e un occOf avec this.ctxs?
        val u = occurrencesOf(terminal)(using env, ctxs)
        val (u2, c, inlinedLet) = ctxs.plugged(inCtxs, u, terminal)

        // TODO: Régler cette affaire
        val expected0 = occurrencesOf(c)(using env, inCtxs)
        val expected = expected0.withRemovedBindings(inlinedLet)
        if (expected != u2) {
          val eq = u2.c2u.toSet.intersect(expected.c2u.toSet)
          val diff = (u2.c2u.toSet ++ expected.c2u.toSet) -- eq
          // if (!env.forceBinding)
          assert(false, "owie, not the same :(")
        }

        assert(codeTpe(terminal) == codeTpe(c), s"${codeTpe(terminal)} != ${codeTpe(c)}")
//        assert(unplugMap.get((c, env)).forall(_ == (this, u2))) // TODO
        // TODO: Dire pk inCtxs est une value et pas une key.
        unplugMap += (c, env) -> (this, u2, inCtxs)
        (u2, c)
      })
    }

    def derived(newTerminal: Code): CodeRes = CodeRes(newTerminal, ctxs.addBoundDef(newTerminal))
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

  // TODO: !!!! Si un Ctxs est ajouté, penser à regarder que toutes les refs soient correctes !!!!
  def negCodeOf(c: Code)(using OEnv): Code = {
    assert(codeTpe(c) == BoolTy, s"Got ${codeTpe(c)}")
    code2sig(c) match {
      case Signature(Label.Not, Seq(cc)) => cc
      case Signature(Label.Lit(BooleanLiteral(b)), Seq()) => b2c(!b)
      case Signature(Label.LessThan, Seq(lhs, rhs)) => codeOfSig(mkGreaterEquals(lhs, rhs), BoolTy)
      case Signature(Label.GreaterEquals, Seq(lhs, rhs)) => codeOfSig(mkLessThan(lhs, rhs), BoolTy)
      case Signature(Label.GreaterThan, Seq(lhs, rhs)) => codeOfSig(mkLessEquals(lhs, rhs), BoolTy)
      case Signature(Label.LessEquals, Seq(lhs, rhs)) => codeOfSig(mkGreaterThan(lhs, rhs), BoolTy)
      case _ =>
        // TODO: Essayer de le push pour IfExpr et MatchExpr
        if (CodeRes.isTerminal(c)) codeOfSig(mkNot(c), BoolTy)
        else {
          // Unplugging a terminal gives the terminal itself, hence we have the above guard.
          unplugged(c) match {
            case Some((cr, _, inCtxs)) =>
              cr.derived(negCodeOf(cr.terminal)).selfPlugged(inCtxs)._2
            case _ => codeOfSig(mkNot(c), BoolTy)
          }
        }
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

  def needsBinding(terminal: Code, terminalComposition: Occurrences, definitionOccurrence: Occurrence)(using env: OEnv, prefix: Ctxs): BindingCase = {
    assert(!isLitOrVar(terminal))
    assert(!prefix.isBoundDef(terminal))

    code2sig(terminal) match {
      case Signature(Label.Ensuring, _) => BindingCase.Inlinable
      case _ =>
        if (env.forceBinding) BindingCase.MustBind
        else {
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
              assert(inCtxs.ctxs(prefix.ctxs.size) == Ctx.BoundDef(terminal))
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
              assert(inCtxs.ctxs(prefix.ctxs.size) == Ctx.BoundDef(terminal))

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
                    case Ctx.BoundDef(defn) =>
                      codePurity(defn)(using env, running).isPure &&
                        rec(extras.tail, running.addBoundDef(defn))
                  }
                }
                val extras = inCtxs.ctxs.drop(prefix.ctxs.size + 1) // +1 car c'est après ce binding
                rec(extras, prefix.addBoundDef(terminal))
              }

              if (!inLambda && isPureSuffix) BindingCase.Inlinable
              else BindingCase.MustBind
          }
        }
    }
  }

  def codeOfExprsBound(es: Seq[Expr], tpe: Type)(cons: Seq[Code] => Signature)(using OEnv, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), tpe))

  def codeOfExprsBound(e1: Expr, tpe: Type)(cons: Code => Signature)(using OEnv, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1), tpe) { case Seq(c1) => cons(c1) }

  def codeOfExprsBound(e1: Expr, e2: Expr, tpe: Type)(cons: (Code, Code) => Signature)(using OEnv, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2), tpe) { case Seq(c1, c2) => cons(c1, c2) }

  def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, tpe: Type)(cons: (Code, Code, Code) => Signature)(using OEnv, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), tpe) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def codeOfExprsBound(es: Seq[Expr])(cons: Seq[Code] => Code)(using env: OEnv, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    val (newCtxs, codeRess) = es.foldLeft((ctxs, Seq.empty[CodeRes])) {
      case ((ctxs, codeResAcc), e) =>
        val codeResE = codeOfExpr(e)(using env, ctxs)
        assert(ctxs.isPrefixOf(codeResE.ctxs))
        (codeResE.ctxs, codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess)(cons)(using env, newCtxs)
  }

  def combineCodeRes(codeRess: Seq[CodeRes], tpe: Type)(cons: Seq[Code] => Signature)(using OEnv, Ctxs): CodeRes =
    combineCodeRes(codeRess)(cs => codeOfSig(cons(cs), tpe))

  def combineCodeRes(cr1: CodeRes, tpe: Type)(cons: Code => Signature)(using env: OEnv): CodeRes =
    combineCodeRes(Seq(cr1)) { case Seq(c1) => codeOfSig(cons(c1), tpe) }(using env, cr1.ctxs)

  def combineCodeRes(cr1: CodeRes, cr2: CodeRes, tpe: Type)(cons: (Code, Code) => Signature)(using env: OEnv): CodeRes =
    combineCodeRes(Seq(cr1, cr2)) { case Seq(c1, c2) => codeOfSig(cons(c1, c2), tpe) }(using env, cr2.ctxs)

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def combineCodeRes(codeRess: Seq[CodeRes])(cons: Seq[Code] => Code)(using env: OEnv, ctxs: Ctxs): CodeRes = {
    assert(codeRess.isEmpty || (ctxs eq codeRess.last.ctxs))
    assert(codeRess.forall(_.ctxs.isPrefixOf(ctxs)))
    assert(codeRess.size <= 1 || codeRess.zip(codeRess.tail).forall { case (prev, cur) => prev.ctxs.isPrefixOf(cur.ctxs) })

    val terminal = cons(codeRess.map(_.terminal))
    // TODO: Etendre ce check à d'autre cas (ensuring, etc.)
    assert(!isLambdaLike(terminal))
    CodeRes(terminal, ctxs.addBoundDef(terminal))
  }

  def freshVarId(name: String, tpe: Type): VarId = idOfVariable(Variable.fresh(name, tpe))

  object CodeRes {
    def isTerminal(c: Code): Boolean = code2sig(c) match {
      // TODO: Ensuring?
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Decreases/* | Label.Ensuring*/ | Label.Let, _) => false
      case _ => true
    }

    def ifExpr(cond: CodeRes, thenn: CodeRes, els: CodeRes, tpe: Type)(using env: OEnv): CodeRes = {
      assert(cond.ctxs.isPrefixOf(thenn.ctxs))
      assert(cond.ctxs.isPrefixOf(els.ctxs))
      val (_, cThenn) = thenn.selfPlugged(cond.ctxs.withCond(cond.terminal))
      val (_, cEls) = els.selfPlugged(cond.ctxs.withCond(negCodeOf(cond.terminal)))
      val terminal = codeOfSig(mkIfExpr(cond.terminal, cThenn, cEls), tpe)
      CodeRes(terminal, cond.ctxs.addBoundDef(terminal))
    }

    // For Lambda, Choose and Forall
    def lambdaLike(lab: Label.LambdaLike, body: CodeRes, tpe: Type)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(body.ctxs))
      val (_, cBody) = body.selfPlugged(ctxs)
      val terminal = codeOfSig(mkLambdaLike(lab, cBody), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    // TODO: On pourrait faire mieux (p.ex. extraire des trucs communs ds body pr en faire beneficier pred)
    def ensuring(body: CodeRes, pred: CodeRes, tpe: Type)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(pred.ctxs))
      assert(ctxs.isPrefixOf(body.ctxs))
      val (_, cBody) = body.selfPlugged(ctxs)
      val (_, cPred) = pred.selfPlugged(ctxs)
      val terminal = code2sig(cPred) match {
        case Signature(Label.Lambda(_), Seq(`trueCode`)) => cBody
        case _ => codeOfSig(mkEnsuring(cBody, cPred), tpe)
      }
      CodeRes(terminal, ctxs)
    }

    def matchExpr(scrut: CodeRes, cases: Seq[CodeResMatchCase], tpe: Type): CodeRes = {
      assert(cases.nonEmpty)
      val terminal = codeOfSig(mkMatchExpr(scrut.terminal, cases.map(_.mc)), tpe)
      CodeRes(terminal, scrut.ctxs.addBoundDef(terminal))
    }

    def err(ofTpe: Type, descr: String, tpe: Type)(using ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkError(ofTpe, descr), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def noTree(ofTpe: Type, tpe: Type)(using ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkNoTree(ofTpe), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }
  }

  def codeOfExpr(e: Expr)(using env: OEnv, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    val tpe = e.getType
    val res = e match {
      case v: Variable =>
        val c = subst.get(v).getOrElse(codeOfVarId(idOfVariable(v)))
        CodeRes(c, ctxs)

      case l: Literal[_] => CodeRes(codeOfLit(l), ctxs)

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val ctxsThen = rcond.ctxs.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using env, ctxsThen)
        val ctxsEls = rcond.ctxs.withCond(negCodeOf(rcond.terminal))
        val rels = codeOfExpr(els)(using env, ctxsEls)
        CodeRes.ifExpr(rcond, rthenn, rels, tpe)

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
        CodeRes.lambdaLike(lab, rbody, tpe)

      case Let(vd, e, body) =>
        val re = codeOfExpr(e)
        assert(re.ctxs.isLitVarOrBoundDef(re.terminal))
        assert(!code2sig(re.terminal).label.isEnsuring)
        codeOfExpr(body)(using env, re.ctxs, subst + (vd.toVariable -> re.terminal))

      case e: (Assume | Assert | Require | Decreases) =>
        val (lab: Label.AssumeLike, pred, body) = e match {
          case Assume(pred, body) => (Label.Assume, pred, body)
          case Assert(pred, _, body) => (Label.Assert, pred, body)
          case Require(pred, body) => (Label.Require, pred, body)
          case Decreases(measure, body) => (Label.Decreases, measure, body)
        }
        val rpred = codeOfExpr(pred)
        assert(rpred.ctxs.isLitVarOrBoundDef(rpred.terminal))
        codeOfExpr(body)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal))

      case Ensuring(body, pred) =>
        // TODO: Ok?
        val rbody = codeOfExpr(body)
        val rpred = codeOfExpr(pred) // Using the default ctxs (not rbody.ctxs)
        CodeRes.ensuring(rbody, rpred, tpe)

      case ADT(id, tps, args) => codeOfExprsBound(args, tpe)(mkADT(id, tps, _))
      case Tuple(args) => codeOfExprsBound(args, tpe)(mkTuple)
      case FunctionInvocation(id, tps, args) => codeOfExprsBound(args, tpe)(mkFunInvoc(id, tps, _))
      case Application(callee, args) => codeOfExprsBound(callee +: args, tpe) { case cCallee +: cArgs => mkApp(cCallee, cArgs) }
      case IsConstructor(e, id) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, tpe)(mkIsCtor(_, adt, id))
      case s @ ADTSelector(e, selector) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, tpe)(mkADTSelector(_, adt, s.constructor, selector))

      // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
      // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
      //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
      //  une map ad-hoc qui contient ces infos...?
      case Annotated(e, flags) =>
        // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
        //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
        //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
        codeOfExprsBound(e, tpe)(mkAnnot(_, flags))

      // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
      case and @ And(_) =>
        val ands = unAnd(and)
        codeOfExpr(Not(Or(ands.map(Not.apply))))
      case or @ Or(_) => transformDisjunction(unOr(or))(codeOfExpr)
      case Not(e) => negExprOf(e)

      case Implies(e1, e2) => codeOfExpr(Or(Not(e1), e2))
      case Equals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkEquals)
      case LessThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessThan)
      case GreaterThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterThan)
      case LessEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessEquals)
      case GreaterEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterEquals)
      case UMinus(e) => codeOfExprsBound(e, tpe)(mkUMinus)
      case Plus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkPlus)
      case Minus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkMinus)
      case Times(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkTimes)
      case Division(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkDivision)
      case Remainder(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkRemainder)
      case Modulo(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkModulo)
      case BVNot(e) => codeOfExprsBound(e, tpe)(mkBVNot)
      case BVAnd(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAnd)
      case BVOr(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVOr)
      case BVXor(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVXor)
      case BVShiftLeft(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVShiftLeft)
      case BVAShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAShiftRight)
      case BVLShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVLShiftRight)
      case BVNarrowingCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVNarrowingCast(_, newTpe))
      case BVWideningCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVWideningCast(_, newTpe))
      case BVUnsignedToSigned(e) => codeOfExprsBound(e, tpe)(mkBVUnsignedToSigned)
      case BVSignedToUnsigned(e) => codeOfExprsBound(e, tpe)(mkBVSignedToUnsigned)
      case TupleSelect(e, index) => codeOfExprsBound(e, tpe)(mkTupleSelect(_, index))
      case FiniteSet(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteSet(_, base))
      case SetAdd(set, elem) => codeOfExprsBound(set, elem, tpe)(mkSetAdd)
      case ElementOfSet(elem, set) => codeOfExprsBound(elem, set, tpe)(mkElementOfSet)
      case SubsetOf(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSubsetOf)
      case SetIntersection(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetIntersection)
      case SetUnion(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetUnion)
      case SetDifference(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetDifference)
      case FiniteArray(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteArray(_, base))
      case LargeArray(elems, default, size, base) => ???
      case ArraySelect(array, index) => codeOfExprsBound(array, index, tpe)(mkArraySelect)
      case ArrayUpdated(array, index, v) => codeOfExprsBound(array, index, v, tpe)(mkArrayUpdated)
      case ArrayLength(array) => codeOfExprsBound(array, tpe)(mkArrayLength)

      case Error(ofTpe, descr) => CodeRes.err(ofTpe, descr, tpe)
      case NoTree(ofTpe) => CodeRes.noTree(ofTpe, tpe)

      // TODO: Passer en revue la pureté: p.ex. si on est pas exhaustif, devrait-on retourner "assumeChecked"?
      case MatchExpr(scrut, cases) =>
        // Ici, on fait qqchose de similaire au IfExpr
        val rscrut = codeOfExpr(scrut)
        assert(codeTpe(rscrut.terminal) == scrut.getType, s"${codeTpe(rscrut.terminal)} != ${scrut.getType}")
        val rcases = signatureOfCases(rscrut.terminal, cases, Seq.empty)(using env, rscrut.ctxs)
        CodeRes.matchExpr(rscrut, rcases, tpe)

      case e =>
        println("computeSignature: Do not know how to handle "+e)
        ???
    }
    assert(ctxs.isPrefixOf(res.ctxs))
    simplifyTopLvl(res)
  }

  case class CodeResMatchCase(mc: LabMatchCase, composition: Occurrences)

  def signatureOfCase(scrut: Code, mc: MatchCase)(using env: OEnv, ctxs0: Ctxs, subst0: LetValSubst): (CodeResMatchCase, Seq[Code]) = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")
    given ô_ô: LetValSubst = sys.error("Carefully select subst")

    def convertPattern(scrut: Code, pat: Pattern, ctxs0: Ctxs, subst0: LetValSubst): (LabelledPattern, Ctxs, LetValSubst) = {
      val ctxs1 = ctxs0.addBoundDef(scrut)
      val subst1 = pat.binder.map(vd => subst0 + (vd.toVariable -> scrut)).getOrElse(subst0)

      pat match {
        case WildcardPattern(_) => (LabelledPattern.Wildcard, ctxs1, subst1)
        case LiteralPattern(_, lit) => (LabelledPattern.Lit(lit), ctxs1, subst1)
        case ADTPattern(_, id, tps, subps) =>
          val subScruts = adtSubscrutinees(scrut, ADTType(id, tps))
          assert(subScruts.size == subps.size)
          val (rsubs, ctxs2, subst2) = subScruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], ctxs1, subst1)) {
            case ((acc, ctxs, subst), (subScrut, subp)) =>
              val (rsub, ctxs2, subst2) = convertPattern(subScrut, subp, ctxs, subst)
              (acc :+ rsub, ctxs2, subst2)
          }
          (LabelledPattern.ADT(id, tps, rsubs), ctxs2, subst2)
        case TuplePattern(_, subps) =>
          val tt@TupleType(_) = codeTpe(scrut)
          val subScruts = tupleSubscrutinees(scrut, tt)
          assert(subScruts.size == subps.size)
          val (rsubs, ctxs2, subst2) = subScruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], ctxs1, subst1)) {
            case ((acc, ctxs, subst), (subScrut, subp)) =>
              val (rsub, ctxs2, subst2) = convertPattern(subScrut, subp, ctxs, subst)
              (acc :+ rsub, ctxs2, subst2)
          }
          (LabelledPattern.TuplePattern(rsubs), ctxs2, subst2)
        case UnapplyPattern(_, recs, id, tps, subps) =>
          ???
      }
    }

    val (labPat, ctxs1, subst1) = convertPattern(scrut, mc.pattern, ctxs0, subst0)
    // patConds: sans le guard!
    val patConds = collectPatternConds(scrut, labPat, recursive = true)(using env, ctxs1)
    val patCtxs = ctxs1.withConds(patConds)

    // TODO: On pourrait conserver le ctx des guard pour le body? En gros, qu'on plug le body dans le ctx de guard
    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using env, patCtxs, subst1))
    val (compGuard, cGuard) = rguard.map(_.selfPlugged(patCtxs)).getOrElse((Occurrences.empty, trueCode))

    val rhsCtxs = patCtxs.withCond(cGuard)
    val rrhs = codeOfExpr(mc.rhs)(using env, rhsCtxs, subst1)
    val (compRhs, rhs) = rrhs.selfPlugged(rhsCtxs)

    val labMc = LabMatchCase(labPat, cGuard, rhs)
    (CodeResMatchCase(labMc, compGuard ++ compRhs), patConds :+ cGuard)
  }

  def signatureOfCases(cScrut: Code, mcs: Seq[MatchCase], acc: Seq[CodeResMatchCase])
                      (using env: OEnv, ctxs: Ctxs, subst: LetValSubst): Seq[CodeResMatchCase] = {
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

  // TODO: Make this work with occurrences
  def transformDisjunction[T](disjs: Seq[T])(f: Ctxs ?=> T => CodeRes)(using env: OEnv, outerCtxs: Ctxs): CodeRes = {
    def rec(disjs: Seq[T], rdisjsAcc: Seq[Code])(using ctxs: Ctxs): Seq[Code] = {
      if (disjs.isEmpty) rdisjsAcc
      else {
        assert(outerCtxs.isPrefixOf(ctxs))
        assert(outerCtxs.bound == ctxs.bound)
        val re = f(disjs.head)
        assert(codeTpe(re.terminal) == BoolTy, s"Got ${codeTpe(re.terminal)}")
        // TODO: Essayer d'extraire autant que possible ici
        // Remarque: c'est bien le ctxs d'origine qu'on utilise,
        // pas celui de re car celui-ci contient des bdgs et d'autres conds (qui ne sont pas carry over)
        val (_, rePlugged) = re.selfPlugged(ctxs)
        val neg = negCodeOf(rePlugged)
//        if (neg == falseCode) rdisjsAcc :+ rePlugged // Pas besoin d'aller plus loin, car on couvre tous les cas
//        else {
          val res = rec(disjs.tail, rdisjsAcc :+ rePlugged)(using ctxs.withCond(neg))
          val noTailRecPls = ctxs.withCond(neg)
          res
//        }
      }
    }

    val rdisjs = rec(disjs, Seq.empty)
    val isPure = rdisjs.forall(c => codePurity(c).isPure)
    val ror = codeOfSig(mkOr(rdisjs), BoolTy)
    CodeRes(ror, outerCtxs.addBoundDef(ror))
//    val ror = simplifiedDisjunction(rdisjs, mayDrop = isPure, mayReorder = isPure) // rooooaaaaarr... ah non c'est pas ça...
//
//    if (rdisjs.contains(ror)) {
//      // rdisjs a été simplifié en un seul disjunct qui a été selfPlugged. On le deplug et le retourne
//      val Some((cr, _, _)) = unplugged(ror)
//      assert(outerCtxs.isPrefixOf(cr.ctxs))
//      cr
//    } else {
//      // Remarque: on retourne le ctx original car les PCs des ors ne sont pas retenues hors des disjunctions.
//      // P.ex. dans val x = b1 || b2 || b3 il serait insensé d'avoir !b1 && !b2 && !b3 dans le env de x.
//      CodeRes(ror, outerCtxs.addBoundDef(ror))
//    }
  }

  // TODO: Voir si on peut pas faire qqchose pr eviter code dup avec pNegNormal
  // Signature de Not(child)
  def negExprOf(child: Expr)(using env: OEnv, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    assert(child.getType == BoolTy)

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
        rchild.derived(negChild)
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

  case class RevEnv(revLetDefs: Map[Code, VarId], inLambda: Boolean) {
    def withLetBounds(vs: Seq[(VarId, Code)]): RevEnv =
      RevEnv(revLetDefs ++ vs.map { case (v, c) => c -> v }.toMap, inLambda)

    def withLetBounds(v: VarId, c: Code): RevEnv =
      RevEnv(revLetDefs + (c -> v), inLambda)
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty, false)
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

      case Signature(Label.Let, Seq(cE, cBody)) =>
        val e = uncodeOf(cE)
        val v = freshVarId("bdg", codeTpe(cE))
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
        recHelper(body)(Lambda(vds, _))(using renv.copy(inLambda = true))
      case Signature(Label.Choose(v), Seq(pred)) => recHelper(pred)(Choose(new ValDef(varId2Var(v)), _))
      case Signature(Label.Forall(params), Seq(pred)) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        recHelper(pred)(Forall(vds, _))

      case Signature(Label.Or, args) => recHelper(args)(Or.apply)
      case Signature(Label.Not, Seq(c)) =>
        code2sig(c) match {
          case Signature(Label.Or, disjs) =>
            given OEnv = OEnv(renv.inLambda, forceBinding = false)
            recHelper(disjs.map(negCodeOf))(And.apply)
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

        def convertPattern(scrut: Code, pat: LabelledPattern, vds: Map[Code, ValDef]): Pattern = {
          def recHelper(subscruts: Seq[Code], subps: Seq[LabelledPattern]): Seq[Pattern] = {
            assert(subscruts.size == subps.size)
            subscruts.zip(subps).map {
              case (subscrut, subpat) => convertPattern(subscrut, subpat, vds)
            }
          }
          val bdg = vds.get(scrut)
          pat match {
            case LabelledPattern.Wildcard => WildcardPattern(bdg)
            case LabelledPattern.ADT(id, tps, subps) =>
              val rsubs = recHelper(adtSubscrutinees(scrut, ADTType(id, tps)), subps)
              ADTPattern(bdg, id, tps, rsubs)
            case LabelledPattern.TuplePattern(subps) =>
              val tt@TupleType(bases) = codeTpe(scrut)
              assert(bases.size == subps.size)
              val rsubs = recHelper(tupleSubscrutinees(scrut, tt), subps)
              TuplePattern(bdg, rsubs)
            case LabelledPattern.Lit(lit) => LiteralPattern(bdg, lit)
            case LabelledPattern.Unapply(recs, id, tps, sub) => ???
          }
        }

        def uncodeOfCase(pat: LabelledPattern, cGuard: Code, cRhs: Code): (Pattern, RevRes, RevRes) = {
          val allScruts = allScrutinees(cScrut, pat)
          val scrutBdgs = allScruts.zipWithIndex.map {
            case (subScrut, i) =>
              val vId = idOfVariable(Variable.fresh(s"bdg$i", codeTpe(subScrut)))
              vId -> subScrut
          }
          val newRenv = renv.withLetBounds(scrutBdgs)
          val guard = uncodeOf(cGuard)(using newRenv)
          val rhs = uncodeOf(cRhs)(using newRenv)
          // On retire les scrut. binding qui sont inutiles.
          val scrutVds = scrutBdgs.filter { case (v, _) => guard.used(v) || rhs.used(v) }
            .map { case (v, c) =>
              val vd = new ValDef(varId2Var(v))
              c -> vd
            }.toMap
          (convertPattern(cScrut, pat, scrutVds), guard, rhs)
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
          given OEnv = OEnv(inLambda = false, forceBinding = true)
          given Ctxs = Ctxs.empty
          given LetValSubst = LetValSubst.empty
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

  def allScrutinees(scrut: Code, pat: LabelledPattern): Seq[Code] = {
    pat match {
      case LabelledPattern.Wildcard | LabelledPattern.Lit(_) => Seq(scrut)
      case LabelledPattern.ADT(id, tps, subps) =>
        val subscruts = adtSubscrutinees(scrut, ADTType(id, tps))
        assert(subscruts.size == subps.size)
        scrut +: subscruts.zip(subps).flatMap {
          case (subscrut, subp) => allScrutinees(subscrut, subp)
        }
      case LabelledPattern.TuplePattern(subps) =>
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        assert(subscruts.size == subps.size)
        scrut +: subscruts.zip(subps).flatMap {
          case (subscrut, subp) => allScrutinees(subscrut, subp)
        }
      case LabelledPattern.Unapply(recs, id, tps, sub) => sys.error("Oh non, un Unapply :(")
    }
  }

  def addScrutineeBindings(scrut: Code, pat: LabelledPattern, ctxs: Ctxs): Ctxs = {
    allScrutinees(scrut, pat).foldLeft(ctxs) {
      case (ctxs, scrut) => ctxs.addBoundDef(scrut)
    }
  }

  // TODO: Ordre ok???
  // TODO: Ordre ok???
  // TODO: Ordre ok???
  def collectPatternConds(scrut: Code, pat: LabelledPattern, recursive: Boolean)(using env: OEnv, ctxs: Ctxs): Seq[Code] = {
    assert(ctxs.isLitVarOrBoundDef(scrut))

    def recHelper(subscruts: Seq[Code], subps: Seq[LabelledPattern], patConds: Seq[Code]): Seq[Code] = {
      assert(subscruts.size == subps.size)
      subscruts.zip(subps).foldLeft((patConds, ctxs.withConds(patConds))) {
        case ((acc, ctxs), (subscrut, subpat)) =>
          val conds2 = collectPatternConds(subscrut, subpat, true)(using env, ctxs)
          (acc ++ conds2, ctxs.withConds(conds2))
      }._1
    }

    pat match {
      case LabelledPattern.Wildcard | LabelledPattern.Lit(_) => Seq.empty
      case LabelledPattern.ADT(id, tps, subps) =>
        val adt = ADTType(id, tps)
        val tcons = getConstructor(id, tps)
        assert(tcons.fields.size == subps.size)
        val patConds = {
          if (isConstructor(scrut, adt, id) == Some(true)) Seq.empty[Code]
          else Seq(codeOfSig(mkIsCtor(scrut, adt, id), BoolTy))
        }
        if (recursive) recHelper(adtSubscrutinees(scrut, adt), subps, patConds)
        else patConds
      case LabelledPattern.TuplePattern(subps) =>
        if (recursive) {
          val tt@TupleType(bases) = codeTpe(scrut)
          assert(bases.size == subps.size)
          val subscruts = tupleSubscrutinees(scrut, tt)
          recHelper(subscruts, subps, Seq.empty)
        }
        else Seq.empty
      case LabelledPattern.Unapply(recs, id, tps, subps) =>
        sys.error(s"Does not know how to handle $pat")
    }
  }

  def isLambda(c: Code): Boolean = code2sig(c).label.isLambda
  def isLambdaLike(c: Code): Boolean = code2sig(c).label.isLambdaLike
  def isVar(c: Code): Boolean = code2sig(c).label.isVar
  def isLitOrVar(c: Code): Boolean = code2sig(c).label.isLitOrVar

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
  def simplifyTopLvl(cr: CodeRes)(using OEnv): CodeRes = {
    given ctxs: Ctxs = cr.ctxs
    val tpe = codeTpe(cr.terminal)
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)

    code2sig(cr.terminal) match {
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
                case Ctx.BoundDef(term) => term == cr.terminal
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
          case Some(b) => cr.derived(b2c(b))
          case None => cr
        }

      case Signature(Label.ADTSelector(_, ctor, sel), Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.ADT(id, _), args) if id == ctor.id =>
            // il se peut dans certains cas que id != ctor.id.
            // p.ex. dans
            //  None() match {
            //    case Some(r) =>
            //      /* utilisation de r, qui va causer ce cas */
            //    case None() =>
            //  }
            // C'est plus tard que cette branche va être éliminée; en attendant, ne paniquons pas!
            // Contentons-nous de ne rien faire et de retourner le résultat inchangé...
            // assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
            val index = ctor.definition.selectorID2Index(sel)
            cr.derived(args(index))
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
            cr.derived(base)
          case None => cr
        }

      case Signature(Label.TupleSelect(ii), Seq(e)) =>
        val i = ii - 1
        code2sig(e) match {
          case Signature(Label.Tuple, args) => cr.derived(args(i))
          case _ => cr
        }

      case Signature(Label.Not, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.Not, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(lab@(Label.Equals | Label.GreaterEquals | Label.LessEquals | Label.LessThan | Label.GreaterThan), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Equals | Label.GreaterEquals | Label.LessEquals => trueCode
          case Label.LessThan | Label.GreaterThan => falseCode
        }
        if (e1 == e2) cr.derived(resIfEq)
        else cr

      case Signature(Label.UMinus, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.UMinus, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(Label.Plus, Seq(e1, e2)) =>
        if (e1 == zero) cr.derived(e2)
        else if (e2 == zero) cr.derived(e1)
        else cr

      case Signature(Label.Minus, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(zero)
        else cr

      case Signature(Label.Times, Seq(e1, e2)) =>
        if (e1 == zero || e2 == zero) cr.derived(zero)
        else if (e1 == one) cr.derived(e2)
        else if (e2 == one) cr.derived(e1)
        else cr

      case Signature(lab@(Label.Division | Label.Remainder | Label.Modulo), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Division => one
          case Label.Remainder | Label.Modulo => zero
        }
        if (opts.assumeChecked && e2 != zero && e1 == zero) cr.derived(zero)
        else if (opts.assumeChecked && e2 != zero && e1 == e2) cr.derived(resIfEq)
        else cr

      case Signature(Label.BVNot, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.BVNot, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(Label.BVAnd, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(e1)
        else if (e1 == zero || e2 == zero) cr.derived(zero)
        else cr

      case Signature(Label.BVOr, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(e1)
        else if (e1 == zero) cr.derived(e2)
        else if (e2 == zero) cr.derived(e1)
        else cr

      case Signature(Label.BVXor, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(zero)
        else if (e1 == zero) cr.derived(e2)
        else if (e2 == zero) cr.derived(e1)
        else cr

      case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
        if (e2 == zero) cr.derived(e1) else cr

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
              case Ctx.BoundDef(term) => term == cr.terminal
              case _ => false
            }, s"Trahison! Trahison! On a $matchCtx !!!")
            val rhsUnpl = unplugged(rhs).get._1
            assert(prevCtxs.isPrefixOf(rhsUnpl.ctxs))
            rhsUnpl

          case SimplifiedCases.Cases(newCases) =>
            val newMatch = codeOfSig(mkMatchExpr(scrut, newCases), tpe)
            cr.derived(newMatch)
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

  def simplifyCase(scrut: Code, matchCase: LabMatchCase)(using env: OEnv, ctxs0: Ctxs): SimplifiedCase = {
    val ctxs1 = addScrutineeBindings(scrut, matchCase.pattern, ctxs0)
    given Ctxs = ctxs1
    val patConds = collectPatternConds(scrut, matchCase.pattern, recursive = true)
    val caseConds = patConds :+ matchCase.guard
    lazy val isRhsPure = codePurity(matchCase.rhs)(using env, ctxs1.withConds(caseConds)).isPure

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
            val wildcard = LabMatchCase(LabelledPattern.Wildcard, cases.head.guard, cases.head.rhs)
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
  def inlineLambda(outerCtxs: Ctxs, argsSubst: Seq[(VarId, Code)], body: Code)(using env: OEnv): CodeRes = {
    // Essentiellement un freshener + simplifyTopLvl a chaque step
    object inliner extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)(using env: OEnv, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val freshParams = lab.params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
          val newLab = lab.replacedParams(freshParams.map(_._2))
          val newLam = codeOfSig(mkLambdaLike(newLab, body), codeTpe(c))
          val rec = super.transformImpl(newLam, repl ++ freshParamsRepl, ())
          simplifyTopLvl(rec)

        case Signature(_, _) =>
          val rec = super.transformImpl(c, repl, ())
          simplifyTopLvl(rec)
      }
    }

    val bodyTpe = codeTpe(body)
    val initCtxs = argsSubst.foldLeft(outerCtxs) {
      case (ctxs, (_, arg)) => ctxs.addBoundDef(arg)
    }
    val initRepl = argsSubst.map { case (param, arg) => codeOfVarId(param) -> arg }.toMap
    val inlined = inliner.transform(body, initRepl, ())(using env, initCtxs)
    assert(codeTpe(inlined.terminal) == bodyTpe)
    inlined
  }

  // TODO: Nom de fn: aussi selon env.varSubst...
  def substByLet(v: VarId)(using ctxs: Ctxs): Option[Code] = {
//    ctxs.varSubstMap.get(v) match {
//      case Some(c) => code2sig(c).label match {
//        case Label.Var(v2) =>
//          // Pas d'alias d'alias etc.
//          assert(!ctxs.varSubstMap.contains(v2))
//          ctxs.boundTo(v2).filterNot(isLambda).orElse(Some(c))
//
//        case lab =>
//          assert(lab.isLiteral)
//          Some(c)
//      }
//      case None => ctxs.boundTo(v).filterNot(isLambda)
//    }
    ???
  }

  class CodePurity extends CodeTryFolder[Unit, Purity] {
    override type Extra = Unit

    private val visiting = mutable.Set.empty[Code]

    def codePurity(c: Code)(using OEnv, Ctxs): Purity = tryFold(c, Pure, ()).getOrElse(Impure)

    override def foldOverPatternConditions: Boolean = true

    override def tryFoldImpl(c: Code, acc: Purity, extra: Unit)(using env: OEnv, ctxs: Ctxs): Either[Unit, Purity] = {
      if (acc == Impure) Left(())
      else if (ctxs.isBoundDef(c)) Right(acc)
      else {
        if (visiting(c)) {
          println(s"!!! Already visited $c  =  ${code2sig(c)}")
        }
        visiting += c
        val purityC = code2sig(c) match {
          case Signature(Label.Var(_) | Label.Lit(_), Seq()) => Pure
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
            // TODO: L'orig ignore callee, mais si on fait ça, on risque de faire du reordering dans certains cas (comme ContMonad)
            // TODO: Dans SWP: quid pureté callee???
            // TODO: Pureté ok? Après tout, un inline de lambda peut donner lieu à impure...
            lazy val calleePurity = code2sig(callee) match {
              case Signature(Label.Lambda(params), Seq(body)) =>
                assert(params.size == args.size)
                codePurity(body)
              case _ => Impure
            }
            assmChkPurity ++ calleePurity ++ fold(args.map(codePurity))

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
  // TODO: Prefer the one of tryFold
  def occurrencesOf(c: Code)(using env: OEnv, ctxs: Ctxs): Occurrences = {
    def occOfCase(scrut: Code, matchCase: LabMatchCase)(using env: OEnv, ctxs0: Ctxs): (Occurrences, Seq[Code]) = {
      val ctxs1 = addScrutineeBindings(scrut, matchCase.pattern, ctxs0)
      val patConds = collectPatternConds(scrut, matchCase.pattern, recursive = true)(using env, ctxs1)
      // Les pattern conditions ne sont pas comptées comme "occurrences"
      val ctxsGuard = ctxs1.withConds(patConds)
      val occGuard = occurrencesOf(matchCase.guard)(using env, ctxsGuard)
      val ctxsRhs = ctxsGuard.withCond(matchCase.guard)
      val occRhs = occurrencesOf(matchCase.rhs)(using env, ctxsRhs)
      (occGuard ++ occRhs, patConds :+ matchCase.guard)
    }
    def occOfCases(scrut: Code, cases: Seq[LabMatchCase], acc: Occurrences)(using env: OEnv, ctxs: Ctxs): Occurrences = {
      if (cases.isEmpty) acc
      else {
        val (occCase, caseConds) = occOfCase(scrut, cases.head)
        val negCaseConds = negatedConjunction(caseConds)
        occOfCases(scrut, cases.tail, acc ++ occCase)(using env, ctxs.withCond(negCaseConds))
      }
    }

    val slf = Occurrences.of(c) // TODO: Hmm, non
    val res = if (ctxs.isBoundDef(c)) slf
    else {
      code2sig(c) match {
        case Signature(Label.Lit(_), Seq()) => Occurrences.empty
        case Signature(Label.Var(_), Seq()) => slf

        case Signature(Label.Let, Seq(e, b)) =>
          assert(CodeRes.isTerminal(e))
          assert(!isLitOrVar(e))
          assert(!ctxs.isBoundDef(e))
          val occE = occurrencesOf(e)
          assert(occE(e).isOnce)
          val occB = occurrencesOf(b)(using env, ctxs.addBoundDef(e))
          (occE ++ occB).setTo(e, Occurrence.Once(ctxs, env.inLambda))

        case Signature(l: Label.AssumeLike, Seq(pred, body)) =>
          assert(CodeRes.isTerminal(pred))
          val occPred = occurrencesOf(pred)
          val occBody = occurrencesOf(body)(using env, ctxs.addBoundDef(pred).withAssumeLike(l, pred))
          occPred ++ occBody

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          slf ++ occurrencesOf(body)(using env.copy(inLambda = env.inLambda || lab.isLambda), ctxs)

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          slf ++ occurrencesOf(body) ++ occurrencesOf(pred)

        case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
          assert(CodeRes.isTerminal(cond))
          val occCond = occurrencesOf(cond)
          val ctxs1 = ctxs.addBoundDef(cond)
          val occThn = occurrencesOf(thn)(using env, ctxs1.withCond(cond))
          val occEls = occurrencesOf(els)(using env, ctxs1.withCond(negCodeOf(cond)))
          slf ++ occCond ++ occThn ++ occEls

        case Signature(Label.Or, disjs) =>
          disjs.foldLeft((ctxs, slf)) {
            case ((ctxs, acc), disj) =>
              given Ctxs = ctxs
              val occDisj = occurrencesOf(disj)
              (ctxs.withCond(negCodeOf(disj)), acc ++ occDisj)
          }._2

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          assert(2 * pats.size == guardRhs.size)
          assert(CodeRes.isTerminal(scrut))
          val cases = pats.zip(guardRhs.grouped(2)).map {
            case (pat, Seq(guard, rhs)) => LabMatchCase(pat, guard, rhs)
            case _ => sys.error("no")
          }
          val occScrut = occurrencesOf(scrut)
          occOfCases(scrut, cases, slf ++ occScrut)(using env, ctxs.addBoundDef(scrut))

        case Signature(_, children) =>
          assert(children.forall(CodeRes.isTerminal))
          children.foldLeft((ctxs, slf)) {
            case ((ctxs, acc), c) =>
              given Ctxs = ctxs
              val occC = occurrencesOf(c)
              (ctxs.addBoundDef(c), acc ++ occC)
          }._2
      }
    }
//    val expected = codeOcc.occOf(c)
//    val eq = expected.c2u.toSet.intersect(res.c2u.toSet)
//    val diff = (expected.c2u.toSet ++ res.c2u.toSet) -- eq
    // assert(res == expected)
    res
  }

  class CodeOccurrences extends CodeTryFolder[Unit, Occurrences] {
    override type Extra = Unit

    override def foldOverPatternConditions: Boolean = false

    def occOf(c: Code)(using env: OEnv, ctxs: Ctxs) =
      tryFold(c, Occurrences.empty, ()).getOrElse(sys.error("impossible"))

    // TODO: If we are careful, we can avoid having to reimplement the cases for "self plugged"
    override def tryFoldImpl(c: Code, acc: Occurrences, extra: Unit)(using env: OEnv, ctxs: Ctxs): Either[Unit, Occurrences] = {
      val slf = Occurrences.of(c)
      if (ctxs.isBoundDef(c)) Right(acc ++ slf)
      else {
        code2sig(c) match {
          case Signature(Label.Lit(_), Seq()) =>
            assert(slf.c2u.isEmpty)
            Right(acc)

          case Signature(Label.Var(_), Seq()) =>
            Right(acc ++ slf)

          case Signature(Label.Let, Seq(e, b)) =>
            assert(CodeRes.isTerminal(e))
            assert(!isLitOrVar(e))
            assert(!ctxs.isBoundDef(e))
            assert(acc(e).isZero)
            val occE = occOf(e)
            assert(occE(e).isOnce)
            val occB = occOf(b)(using env, ctxs.addBoundDef(e))
            Right((acc ++ occE ++ occB).setTo(e, Occurrence.Once(ctxs, env.inLambda)))

          case Signature(l: Label.AssumeLike, Seq(pred, body)) =>
            assert(CodeRes.isTerminal(pred))
            val occPred = occOf(pred)
            val occBody = occOf(body)(using env, ctxs.addBoundDef(pred).withAssumeLike(l, pred))
            Right(acc ++ occPred ++ occBody)

          // TODO: Remarque: Pour les expressions avec "self plugged", on ne "thread" pas les occurences
          case Signature(Label.Ensuring, Seq(body, pred)) =>
            assert(acc.c2u.isEmpty)
            val occBody = occOf(body)
            val occPred = occOf(pred)
            Right(slf ++ acc ++ occBody ++ occPred)

          case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
            assert(CodeRes.isTerminal(cond))
            val occCond = occOf(cond)
            val ctxs1 = ctxs.addBoundDef(cond)
            val occThn = occOf(thn)(using env, ctxs1.withCond(cond))
            val occEls = occOf(els)(using env, ctxs1.withCond(negCodeOf(cond)))
            Right(slf ++ occCond ++ occThn ++ occEls)

          // TODO: Match case

          case _ =>
            super.tryFoldImpl(c, acc ++ slf, ())
        }
      }
    }
  }

  // TODO: Commentaire à propos de code potentiel dans les labels qui ne sont pas transform
  class CodeTransformer {
    type Extra

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      val res = repl.get(c) match {
        case Some(cc) =>
          assert(ctxs.isLitVarOrBoundDef(cc), "repl fait référence à un code qui n'est pas let-bound!!!")
          CodeRes(cc, ctxs)
        case None =>
          transformImpl(c, repl, extra)
      }
      assert(ctxs.isPrefixOf(res.ctxs))
      assert(isLambda(c) == isLambda(res.terminal))
      res
    }

    def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      val tpe = codeTpe(c)
      assert(!repl.contains(c), s"$c = ${code2sig(c)} n'a pas été remplacé par transform")

      code2sig(c) match {
        case Signature(Label.Var(_) | Label.Lit(_), Seq()) => CodeRes(c, ctxs)

        case Signature(Label.Let, Seq(e, b)) =>
          assert(CodeRes.isTerminal(e))
          assert(!isLitOrVar(e))
          assert(!ctxs.isBoundDef(e))
          val re = transform(e, repl, extra)
          assert(re.ctxs.isLitVarOrBoundDef(re.terminal))
          transform(b, repl + (e -> re.terminal), extra)(using env, re.ctxs)

        case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
          assert(CodeRes.isTerminal(cond))
          val rcond = transform(cond, repl, extra)
          val thennCtxs = rcond.ctxs.withCond(rcond.terminal)
          val rthenn = transform(thenn, repl, extra)(using env, thennCtxs)
          val elsCtxs = rcond.ctxs.withCond(negCodeOf(rcond.terminal)) // (using rcond.env)
          val rels = transform(els, repl, extra)(using env, elsCtxs)
          CodeRes.ifExpr(rcond, rthenn, rels, tpe)

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val rbody = transform(body, repl, extra)(using env.copy(inLambda = env.inLambda || lab.isLambda))
          CodeRes.lambdaLike(lab, rbody, tpe)

        case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
          assert(CodeRes.isTerminal(pred))
          val rpred = transform(pred, repl, extra)
          assert(rpred.ctxs.isLitVarOrBoundDef(rpred.terminal))
          transform(body, repl, extra)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal))

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          // TODO: Ok?
          val rbody = transform(body, repl, extra)
          val rpred = transform(pred, repl, extra)
          CodeRes.ensuring(rbody, rpred, tpe)

        case Signature(Label.Or, disjs) =>
          transformDisjunction(disjs)(transform(_, repl, extra))

        case Signature(Label.Error(ofTpe, descr), Seq()) =>
          CodeRes.err(ofTpe, descr, tpe)
        case Signature(Label.NoTree(ofTpe), Seq()) =>
          CodeRes.noTree(ofTpe, tpe)

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          assert(2 * pats.size == guardRhs.size)
          assert(CodeRes.isTerminal(scrut))
          val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
          val cases = pats.zip(guards).zip(rhss).map {
            case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
          }
          val rscrut = transform(scrut, repl, extra)
          assert(rscrut.ctxs.isLitVarOrBoundDef(rscrut.terminal))
          // TODO: !!! Si rscrut est une var/lit !!! ?
          // TODO: !!! Si rscrut est une var/lit !!! ?
          // TODO: !!! Si rscrut est une var/lit !!! ?
          val rcases = transformCases(scrut, rscrut.terminal, cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using env, rscrut.ctxs)
          CodeRes.matchExpr(rscrut, rcases, tpe)

        // TODO: Que pour les cas triviaux où env est le même, bindings std, etc.
        case Signature(lab, children) => transformSeq(children, tpe, repl, extra)(Signature(lab, _))
      }
    }

    final def transformSeq(cs: Seq[Code], tpe: Type, repl: Map[Code, Code], extra: Extra)
                          (mkSig: Seq[Code] => Signature)(using env: OEnv, ctxs: Ctxs): CodeRes = {
      given x_x: Ctxs = sys.error("Carefully select ctxs")
      val (newCtxs, ress) = cs.foldLeft((ctxs, Seq.empty[CodeRes])) {
        case ((ctxs, codeResAcc), c) =>
          assert(CodeRes.isTerminal(c))
          val res = transform(c, repl, extra)(using env, ctxs)
          assert(ctxs.isPrefixOf(res.ctxs))
          (res.ctxs, codeResAcc :+ res)
      }
      combineCodeRes(ress, tpe)(mkSig)(using env, newCtxs)
    }

    // TODO: Ok????
    // TODO: Ok????
    // TODO: Ok????
    def transformCase(oldScrut: Code, newScrut: Code, matchCase: LabMatchCase, repl0: Map[Code, Code], extra: Extra)
                     (using env: OEnv, ctxs0: Ctxs): (CodeResMatchCase, Seq[Code]) = {
      assert(repl0.get(oldScrut) == Some(newScrut), s"'repl0' ne contient pas $oldScrut -> $newScrut")
      val oldBdgs = allScrutinees(oldScrut, matchCase.pattern)
      val newBdgs = allScrutinees(newScrut, matchCase.pattern)
      assert(oldBdgs.size == newBdgs.size)
      val repl = repl0 ++ oldBdgs.zip(newBdgs).toMap
      val ctxs1 = addScrutineeBindings(newScrut, matchCase.pattern, ctxs0)
      val patConds = collectPatternConds(newScrut, matchCase.pattern, recursive = true)(using env, ctxs1)
      val patCtxs = ctxs1.withConds(patConds)

      val rguard = transform(matchCase.guard, repl, extra)(using env, patCtxs)
      val (compGuard, cGuard) = rguard.selfPlugged(patCtxs)

      val ctxsRhs = patCtxs.withCond(cGuard)
      val rrhs = transform(matchCase.rhs, repl, extra)(using env, ctxsRhs)
      val (compRhs, cRhs) = rrhs.selfPlugged(ctxsRhs)

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

  trait CodeTryFolder[E, T] {
    type Extra

    final def tryFold(c: Code, acc: T, extra: Extra)(using env: OEnv, ctxs: Ctxs): Either[E, T] =
      tryFoldImpl(c, acc, extra)

    def tryFoldImpl(c: Code, acc: T, extra: Extra)(using env: OEnv, ctxs: Ctxs): Either[E, T] = code2sig(c) match {
      case Signature(Label.Lit(_) | Label.Var(_), Seq()) => Right(acc)

      case Signature(Label.Let, Seq(e, b)) =>
        assert(CodeRes.isTerminal(e))
        assert(!isLitOrVar(e))
        assert(!ctxs.isBoundDef(e))
        for {
          re <- tryFold(e, acc, extra)
          rb <- tryFold(b, re, extra)(using env, ctxs.addBoundDef(e))
        } yield rb

      case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
        assert(CodeRes.isTerminal(pred))
        for {
          rpred <- tryFold(pred, acc, extra)
          rbody <- tryFold(body, rpred, extra)(using env, ctxs.addBoundDef(pred).withAssumeLike(lab, pred))
        } yield rbody

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        assert(CodeRes.isTerminal(cond))
        for {
          rcond <- tryFold(cond, acc, extra)
          ctxs1 = ctxs.addBoundDef(cond)
          rthn <- tryFold(thn, rcond, extra)(using env, ctxs1.withCond(cond))
          rels <- tryFold(els, rthn, extra)(using env, ctxs1.withCond(negCodeOf(cond)))
        } yield rels

      case Signature(Label.Or, args) =>
        tryFoldSeq(args, acc, extra) { case (disj, ctxs) => ctxs.withCond(negCodeOf(disj)) }

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        for {
          rbody <- tryFold(body, acc, extra)
          rpred <- tryFold(pred, rbody, extra)
        } yield rpred

      case Signature(lab: Label.LambdaLike, Seq(body)) =>
        tryFold(body, acc, extra)(using env.copy(inLambda = env.inLambda || lab.isLambda), ctxs)

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        assert(CodeRes.isTerminal(scrut))
        val cases = pats.zip(guardRhs.grouped(2)).map {
          case (pat, Seq(guard, rhs)) => LabMatchCase(pat, guard, rhs)
          case _ => sys.error("oh non, je ne sais pas compter :(")
        }
        for {
          rscrut <- tryFold(scrut, acc, extra)
          rcases <- tryFoldCases(scrut, cases, rscrut, extra)(using env, ctxs.addBoundDef(scrut))
        } yield rcases

      // TODO: Suppose que lab pas besoin d'avoir des sous parties transformées. P.ex. pour MatchExpr, cela ne jouera pas (en raison des recs?)
      case Signature(_, children) =>
        assert(children.forall(CodeRes.isTerminal))
        tryFoldSeq(children, acc, extra)((c, ctxs) => ctxs.addBoundDef(c))
    }

    def foldOverPatternConditions: Boolean

    def tryFoldCase(scrut: Code, matchCase: LabMatchCase, acc: T, extra: Extra)(using env: OEnv, ctxs0: Ctxs): Either[E, (T, Seq[Code])] = {
      val ctxs1 = addScrutineeBindings(scrut, matchCase.pattern, ctxs0)
      val patConds = collectPatternConds(scrut, matchCase.pattern, recursive = true)(using env, ctxs1)
      for {
        rpatConds <-
          if (foldOverPatternConditions) tryFoldSeq(patConds, acc, extra)(using env, ctxs1)
          else Right(acc)
        ctxsGuard = ctxs1.withConds(patConds)
        rguard <- tryFold(matchCase.guard, rpatConds, extra)(using env, ctxsGuard)
        ctxsRhs = ctxsGuard.withCond(matchCase.guard)
        rrhs <- tryFold(matchCase.rhs, rguard, extra)(using env, ctxsRhs)
      } yield (rrhs, patConds :+ matchCase.guard)
    }

    def tryFoldCases(scrut: Code, cases: Seq[LabMatchCase], acc: T, extra: Extra)(using env: OEnv, ctxs: Ctxs): Either[E, T] = {
      if (cases.isEmpty) Right(acc)
      else {
        tryFoldCase(scrut, cases.head, acc, extra).flatMap {
          case (rcase, caseConds) =>
            val negCaseConds = negatedConjunction(caseConds)
            tryFoldCases(scrut, cases.tail, rcase, extra)(using env, ctxs.withCond(negCaseConds))
        }
      }
    }

    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(using OEnv, Ctxs): Either[E, T] =
      tryFoldSeq(cs, acc, extra)((c, ctxs) => ctxs)

    // TODO: Dire que le nextCtxs est appliqué pour le suivant (et pas pr le "current")
    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(nextCtxs: (Code, Ctxs) => Ctxs)(using env: OEnv, ctxs: Ctxs): Either[E, T] = {
      cs.foldLeft(Right((acc, ctxs)): Either[E, (T, Ctxs)]) {
        case (Right((acc, ctxs)), c) =>
          given Ctxs = ctxs
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