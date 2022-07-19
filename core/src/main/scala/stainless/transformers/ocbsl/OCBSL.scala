package stainless
package transformers
package ocbsl

import inox.solvers

// TODO: Certains Or ne semble pas correctement être flattened
trait OCBSL extends Definitions {
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable // A bit ironic that we import mutable stuff right after "Purity"...

  // Not for sparing allocations, but for sparing key strokes :p
  val BoolTy: Type = BooleanType()


  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class OEnv(conditions: Set[Code],
                  letDef: Map[VarId, (Code, Boolean)],
                  forceBinding: Boolean) {
    def withCond(c: Code): OEnv = copy(conditions = conditions + c)
    def withConds(cs: Set[Code]): OEnv = copy(conditions = conditions ++ cs)

    def withLetBound(v: VarId, c: Code, canSubst: Boolean): OEnv = copy(letDef = letDef + (v -> (c, canSubst)))

    def withLetBounds(vs: Seq[(VarId, Code)], canSubst: Boolean): OEnv = withLetBounds(vs)((_, _) => canSubst)

    def withLetBounds(vs: Seq[(VarId, Code)])(canSubst: (VarId, Code) => Boolean): OEnv = {
      assert(letDef.keySet.intersect(vs.map(_._1).toSet).isEmpty)
      OEnv(conditions, letDef ++ vs.map { case (v, c) => v -> (c, canSubst(v, c)) }, forceBinding)
    }

    def isBound(c: Code): Boolean = letDef.exists(_._2._1 == c)
  }

  object OEnv {
    def empty: OEnv = OEnv(Set.empty, Map.empty, false)
  }

  case class InLambda(v: Boolean) {
    def ||(other: Boolean): InLambda = InLambda(v || other)
    def ||(other: InLambda): InLambda = InLambda(v || other.v)
  }

  enum Ctx {
    case Id
    case Let(vId: VarId, eTerminal: Code, eTerminalHasLambda: Boolean, eUsgs: Usages, eEnv: OEnv, canSubst: Boolean)
    case UnboundExpr(terminal: Code, subUsgs: Usages)
    case AssumeLike(lab: Label.AssumeLike, predTerminal: Code, predUsgs: Usages)

    // TODO: Et dans les usgs? Devrait-on regarder là dedans aussi?
    def contains(c: Code): Boolean = this match {
      case Ctx.Id => false
      case Ctx.Let(_, eTerminal, _, _, _, _) => eTerminal == c
      case Ctx.UnboundExpr(terminal, _) => terminal == c
      case Ctx.AssumeLike(_, predTerminal, _) => predTerminal == c // TODO: Est-ce ce qu'on souhaite vraiment?
    }

    def containsBoundVar(v: VarId): Boolean = this match {
      case Ctx.Let(v2, _, _, _, _, _) => v == v2
      case _ => false
    }

    def plugged(u: Usages, c: Code)(using inLambda: InLambda): (Usages, Code) = this match {
      case Ctx.Id => (u, c)

      case Ctx.Let(vId, eTerminal, eTerminalHasLambda, eUsgs, eEnv, canSubst) =>
        // TODO: Rappel: pr les lambdas, le code utilisé est celui de vId, pas de e.terminal!
        val eOcc = u(if (canSubst) eTerminal else codeOfVarId(vId))
        val bdgCase = needsBinding(eTerminal, eTerminalHasLambda, eOcc)(using eEnv)
        if (bdgCase == BindingCase.MustBind || (!canSubst && bdgCase == BindingCase.Inlinable)) {
          val cLet = codeOfSig(mkLet(vId, eTerminal, c), codeTpe(c))
          val u2 = (u ++ eUsgs).setTo(eTerminal, Occurrence.Once(eEnv, inLambda.v))
          (u2, cLet)
        } else {
          val u2 = {
            if (eOcc.isZero) u
            else u ++ eUsgs
          }
          (u2, c)
        }

      case Ctx.UnboundExpr(terminal, subUsgs) =>
        val terminalOcc = u(terminal)
        val u2 = {
          if (terminalOcc.isZero) u
          else if (terminalOcc.isMany) u ++ subUsgs.manyied
          else u ++ subUsgs
        }
        (u2, c)

      case Ctx.AssumeLike(lab, predTerminal, predUsgs) =>
        val c2 = codeOfSig(mkAssumeLike(lab, predTerminal, c), codeTpe(c))
        (u ++ predUsgs, c2)
    }
  }

  case class Ctxs(ctxs: Seq[Ctx]) {
    def pop: Option[(Ctxs, Ctx)] = {
      if (ctxs.isEmpty) None
      else Some((Ctxs(ctxs.init), ctxs.last))
    }
    def popOrId: (Ctxs, Ctx) = pop.getOrElse((Ctxs(Seq.empty), Ctx.Id))

    def :+(ctx: Ctx): Ctxs = Ctxs(ctxs :+ ctx)
    def ++(that: Ctxs): Ctxs = Ctxs(ctxs ++ that.ctxs)

    // TODO: Env ok? Ou faut-il "l'accumuler"?
    def plugged(u: Usages, c: Code)(using InLambda): (Usages, Code) =
      ctxs.foldRight((u, c)) { case (ctx, (u, c)) => ctx.plugged(u, c) }

    def containsBoundVar(v: VarId): Boolean = ctxs.exists(_.containsBoundVar(v))
    def contains(c: Code): Boolean = ctxs.exists(_.contains(c))
  }
  object Ctxs {
    @annotation.targetName("applySeq")
    def apply(ctxs: Ctx*): Ctxs = new Ctxs(ctxs.toSeq)

    def empty: Ctxs = Ctxs(Seq.empty)
  }

  enum Occurrence {
    case Zero
    case Once(inEnv: OEnv, inLambda: Boolean)
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
  }

  case class Usages(c2u: Map[Code, Occurrence]) {
    def apply(c: Code): Occurrence = c2u.getOrElse(c, Occurrence.Zero)

    def ++(that: Usages): Usages = Usages((c2u.keySet ++ that.c2u.keySet)
      .map(c => c -> (this(c) ++ that(c))).toMap)

    def incOccurrences(cs: Iterable[Code])(using inEnv: OEnv, inLambda: InLambda): Usages =
      this ++ Usages(cs.map(c => c -> (Occurrence.Once(inEnv, inLambda.v): Occurrence)).toMap)

    def incOccurrences(cs: Iterable[(Code, OEnv)])(using inLambda: InLambda): Usages =
      this ++ Usages(cs.map { case (c, inEnv) => c -> (Occurrence.Once(inEnv, inLambda.v): Occurrence) }.toMap)

    def incOccurrence(c: Code)(using inEnv: OEnv, inLambda: InLambda): Usages = incOccurrences(Seq(c))

    def setTo(c: Code, o: Occurrence): Usages = Usages(c2u + (c -> o))

    // TODO: What is this name!!!!
    def manyied: Usages = Usages(c2u.map {
      case (c, Occurrence.Zero) => (c, Occurrence.Zero) // TODO: Should we just filter these out?
      case (c, _) => c -> Occurrence.Many
    })
  }

  object Usages {
    def empty: Usages = Usages(Map.empty)

    def of(c: Code)(using env: OEnv, inLambda: InLambda): Usages = of(Seq(c))

    def of(cs: Seq[Code])(using env: OEnv, inLambda: InLambda): Usages =
      Usages(cs.map(c => c -> Occurrence.Once(env, inLambda.v)).toMap) // TODO: Ignorer les lits
  }


  private val unplugMap = mutable.Map.empty[Code, (CodeRes, Usages)]

  // OEnv: En gros tous les "let bindings" des arguments pour terminal (qui peuvent être elided)
  // terminalHasLambdaDef: contient ou est un lambda soit meme
  case class CodeRes(terminal: Code,
                     terminalHasLambdaDef: Boolean,
                     ctxs: Ctxs,
                     usages: Usages,
                     env: OEnv) {
    assert(CodeRes.isTerminal(terminal), s"Gag: $terminal n'est pas un terminal (est un ${code2sig(terminal)})")

    lazy val selfPlugged: (Usages, Code) = {
      // TODO: In lambda même si on apparait dans une lambda?
      val u = Usages.of(terminal)(using env, InLambda(false))
      val (u2, c) = ctxs.plugged(u, terminal)(using InLambda(false))
      assert(codeTpe(terminal) == codeTpe(c), s"${codeTpe(terminal)} != ${codeTpe(c)}")
      unplugMap += c -> (this, u2) // TODO: Quid collision?
      (u2, c)
    }

    def derived(newTerminal: Code)(using InLambda): CodeRes = derived(newTerminal, isLambda(newTerminal)) // TODO: !!!!

    def derived(newTerminal: Code, newTermHasLambdaDef: Boolean)(using InLambda): CodeRes = {
      // TODO: Ok?
      given OEnv = env
      val newSig = code2sig(newTerminal)
      // println(s"Dérivé de $newSig  (ancien terminal = ${code2sig(terminal)})")

      // On valide le nouveau
      assert(CodeRes.isTerminal(newTerminal), s"Gag: le nouveau terminal $newTerminal n'est pas un terminal (est un ${code2sig(newTerminal)})")

      // TODO !!! Quid des comptes des children des children etc. ????
      // TODO !!! Quid des comptes des children des children etc. ????
      val newUsgs = newSig.children
        .map { c =>
          code2sig(c) match {
            case Signature(Label.Lit(_), Seq()) => Usages.empty
            case Signature(Label.Var(v), Seq()) =>
              // TODO: Pas forcément, c'est p-e une free var
              // assert(ctxs.containsBoundVar(v), s"$v pas contenu dans $ctxs")
              Usages.of(c)
            case _ => unplugMap.get(c) match {
              case Some((cCr, cUsgs)) =>
                //// TODO: Devrait-on inclure c? -> non, car déjà inclus au plugging
                //   -> non, c'est cCr.terminal qui est inclu
                // TODO: Ajouter des checks, mais c'est les match expr qui posent problème...
                // assert(cUsgs(c).nonZero, s"$c = ${code2sig(c)})n'apparait pas dans $cUsgs")
//                val free = cUsgs.c2u.keySet.filterNot(cCr.ctxs.contains)
//                assert(free.forall(ctxs.contains), s"$free n'apparaissent pas dans $ctxs")
                cUsgs
              case _ =>
                assert(ctxs.contains(c), s"$c n'apparait nul part dans les contextes précédents: $ctxs")
                Usages.of(c)
            }
          }
        }
//        .map(c => unplugMap.get(c).map(_._2).getOrElse(Usages.of(c)))
        .foldLeft(Usages.empty)(_ ++ _)

      val newCtx = newSig match {
        case Signature(Label.Lambda(_) | Label.Choose(_) | Label.Forall(_) | Label.Ensuring, _) =>
          // val (bodyUnpl, bodyUsgs) = unplugMap(body)  // TODO: bodyUsgs comprend body dans les usages. ok?
          // combinedUnboundCtx(newTerminal)(Seq(ctx))(_ ++ newUsgs)
          Ctx.UnboundExpr(newTerminal, newUsgs)
        case Signature(_, _) =>
          Ctx.Let(freshVarId("bdg", codeTpe(newTerminal)), newTerminal, newTermHasLambdaDef, newUsgs, env, canSubst = true)
          // combinedBindingCtx(newTerminal, newTermHasLambdaDef)(Seq(ctx))(_ ++ newUsgs)
      }
      CodeRes(newTerminal, newTermHasLambdaDef, ctxs :+ newCtx, Usages.empty, env)
    }
  }

  case class CodeResMatchCase(mc: LabMatchCase, usages: Usages, hasLambdaDef: Boolean) // Usages provenant de guard et rhs plugged

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

  // TODO: fusionner les deux fns?
  def codeOfExpr(e: Expr)(using OEnv, InLambda): CodeRes = {
//    if (e.getType == BoolTy) simplifiedDisjunction(pDisj(e).toSet)
//    else {
//      val sig = sigOfExpr(e)
//      codeOfSig(sig, e.getType)
//    }
    // TODO: fusionner les deux fns?
    sigOfExpr(e)
  }

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
  def simplifiedDisjunction(disj0: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, InLambda): Code = {
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
//    codeOfSig(mkOr(disj), BoolTy)
  }

  enum BindingCase {
    // In let v = e in body...
    case Elidable // ... the `e` (and the let) can be removed (that is, we can just return `body`, `e` is pure)
    case Inlinable // ... the `e` can be inlined or bound, but it definitely appears in `body` (may or may not be impure)
    case MustBind // ... the `e` must be bound (appears in `body` if pure, may not appear if impure)
  }

  // TODO: Puisque c'est un terminal, comment peut-il "contenir" un lambda? -> p.ex. par le moyen de if, assume, etc. tout ces trucs
  def needsBinding(terminal: Code, terminalHasLambdaDef: Boolean, occ: Occurrence)(using env: OEnv, inLambda: InLambda): BindingCase = {
    code2sig(terminal) match {
      case Signature(Label.Lit(_) | Label.Var(_), _) => BindingCase.Elidable
      case _ =>
        if (env.forceBinding) BindingCase.MustBind
        else {
          lazy val isPure = codePurity(terminal).isPure
          occ match {
            case Occurrence.Many => BindingCase.MustBind
            case Occurrence.Zero =>
              // Si une expr impure n'apparait pas dans le body, on ne peut pas l'éliminer, il faut donc le bind
              if (!isPure) BindingCase.MustBind
              else BindingCase.Elidable
            case Occurrence.Once(_, inLambda) if isPure =>
              if (inLambda && terminalHasLambdaDef) BindingCase.MustBind
              else BindingCase.Inlinable
            case Occurrence.Once(inEnv, inLambda) =>
              // inEnv représente l'env. actif lors de l'occurrence de `terminal` dans le trou que l'on s'apprête à compléter.
              // S'il est différent de l'env ou `terminal` est introduit, alors on a besoin de let-bind, car inline
              // une expr impure après un PC est incorrect.
              if ((inEnv != env) || inLambda) BindingCase.MustBind
              else BindingCase.Inlinable
          }
        }
    }
  }

  // TODO: Quid simplif???
  def codeOfExprsBound(es: Seq[Expr], consTpe: Type)(cons: Seq[Code] => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), consTpe))

  def codeOfExprsBound(e1: Expr, consTpe: Type)(cons: Code => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1), consTpe) { case Seq(c1) => cons(c1) }

  def codeOfExprsBound(e1: Expr, e2: Expr, consTpe: Type)(cons: (Code, Code) => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1, e2), consTpe) { case Seq(c1, c2) => cons(c1, c2) }

  def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, consTpe: Type)(cons: (Code, Code, Code) => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), consTpe) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def codeOfExprsBound(es: Seq[Expr])(cons: Seq[Code] => Code)(using env: OEnv, inLambda: InLambda): CodeRes = {
    given x_x: OEnv = sys.error("Carefully select env")

    val (newEnv, codeRess) = es.foldLeft((env, Seq.empty[CodeRes])) {
      case ((env, codeResAcc), e) =>
        val codeResE = codeOfExpr(e)(using env)
        (codeResE.env, codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess)(cons)(using newEnv)
  }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def combineCodeRes(codeRess: Seq[CodeRes])(cons: Seq[Code] => Code)(using env: OEnv, inLambda: InLambda): CodeRes = {
    assert(codeRess.isEmpty || (env eq codeRess.last.env))
    val subterms = codeRess.map(_.terminal)
    val terminalContainsLam = codeRess.exists(_.terminalHasLambdaDef)
    val terminal = cons(subterms)

    val ctx = Ctx.Let(freshVarId("bdg", codeTpe(terminal)), terminal, terminalContainsLam, Usages.of(subterms), env, canSubst = true)
    val ctxs = codeRess.map(_.ctxs).foldLeft(Ctxs.empty)(_ ++ _) :+ ctx
    // TODO: Usages de terminal???
    CodeRes(terminal, terminalContainsLam, ctxs, codeRess.foldLeft(Usages.of(terminal))(_ ++ _.usages), env)
  }

  def combineCodeRes(codeRess: Seq[CodeRes], tpe: Type)(cons: Seq[Code] => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    combineCodeRes(codeRess)(cs => codeOfSig(cons(cs), tpe))

  def combineCodeRes(cr1: CodeRes, tpe: Type)(cons: Code => Signature)(using InLambda): CodeRes =
    combineCodeRes(Seq(cr1)) { case Seq(c1) => codeOfSig(cons(c1), tpe) } (using cr1.env)

  def combineCodeRes(cr1: CodeRes, cr2: CodeRes, tpe: Type)(cons: (Code, Code) => Signature)(using InLambda): CodeRes =
    combineCodeRes(Seq(cr1, cr2)) { case Seq(c1, c2) => codeOfSig(cons(c1, c2), tpe) } (using cr2.env)

  def freshVarId(name: String, tpe: Type): VarId = idOfVariable(Variable.fresh(name, tpe))

  def idCtx(u: Usages, c: Code): (Usages, Code) = (u, c)

  object CodeRes {
    // TODO: Dire qu'est-ce que c'est que ce truc!!!!
    def of(term: Code, termHasLambdaDef: Boolean)(using env: OEnv, inLambda: InLambda): CodeRes = {
      CodeRes(term, termHasLambdaDef, Ctxs(Ctx.Id), Usages.of(term), env)
    }

    def isTerminal(c: Code): Boolean = code2sig(c) match {
      // TODO: Ensuring?
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Decreases/* | Label.Ensuring*/ | Label.Let(_), _) => false
      case _ => true
    }

    /*
    // TODO: Dire "elidable"
    def letCtx(vId: VarId, e: CodeRes, b: CodeRes, canSubst: Boolean)(using inLambda: InLambda)(u: Usages, c: Code): (Usages, Code) = {
      /*val (u2, c2) = b.ctx(u, c)
      // TODO: Rappel: pr les lambdas, le code utilisé est celui de vId, pas de e.terminal!
      val eOcc = u2(if (canSubst) e.terminal else codeOfVarId(vId))
      // Pour `e`, on utilise l'environnement dans lequel il a été construit, donc e.env
      val bdgCase = needsBinding(e.terminal, e.terminalHasLambdaDef, eOcc)(using e.env)
      if (bdgCase == BindingCase.MustBind || (!canSubst && bdgCase == BindingCase.Inlinable)) {
        val cLet = codeOfSig(mkLet(vId, e.terminal, c2), codeTpe(c2))
        val u3 = u2.setTo(e.terminal, Occurrence.Once(e.env, inLambda.v))
        e.ctx(u3, cLet)
      } else {
        e.ctx(u2, c2)
      }
      */
      ???
    }
    */

    // TODO: Dire "elidable"
    def let(vId: VarId, e: CodeRes, b: CodeRes, canSubst: Boolean)(using InLambda): CodeRes = {
//      val ctx = letCtx(vId, e, b, canSubst)
      // TODO: Usages.empty ok? Car déjà "compté" par e.ctxs non?
      val ctxs = (e.ctxs :+ Ctx.Let(vId, e.terminal, e.terminalHasLambdaDef, Usages.empty, e.env, canSubst)) ++ b.ctxs
      // TODO: terminalHasLambdaDef ok?
      CodeRes(b.terminal, b.terminalHasLambdaDef, ctxs, b.usages, b.env)
    }

    def ifExpr(cond: CodeRes, thenn: CodeRes, els: CodeRes, tpe: Type)(using InLambda): CodeRes = {
      val uCond = Usages.of(cond.terminal)(using cond.env)
      val (uThenn, cThenn) = thenn.selfPlugged
      val (uEls, cEls) = els.selfPlugged
      val terminal = codeOfSig(mkIfExpr(cond.terminal, cThenn, cEls), tpe)
      val termContainsLam = cond.terminalHasLambdaDef || thenn.terminalHasLambdaDef || els.terminalHasLambdaDef
      // TODO: Devrait-on aussi compter uCond?
      val ctxs = cond.ctxs :+ Ctx.Let(freshVarId("bdgIf", tpe), terminal, termContainsLam, uCond ++ uThenn ++ uEls, cond.env, canSubst = true)
//      val ctx = combinedBindingCtx(terminal, termContainsLam)(Seq(cond.ctx))(_ ++ uCond ++ uThenn ++ uEls)(using cond.env)
      CodeRes(terminal, termContainsLam, ctxs, uCond ++ uThenn ++ uEls ++ Usages.of(terminal)(using cond.env), cond.env)
    }

    // For Lambda, Choose and Forall
    def lambdaLike(body: CodeRes, tpe: Type, isActuallyLambda: Boolean)(mkSig: Code => Signature)(using env: OEnv, inLambda: InLambda): CodeRes = {
      val (usgs, cBody) = body.selfPlugged
      val cLamLike = codeOfSig(mkSig(cBody), tpe)
      // TODO: Ok?
      // TODO: Souhaite-on vraiment bind des lambdas etc. en cas d'égalité???
      // val ctx = combinedBindingCtx(cLamLike, isActuallyLambda)(Seq(idCtx))(_ ++ usgs)
//      val ctx = combinedUnboundCtx(cLamLike)(Seq(idCtx))(_ ++ usgs)
      val ctxs = Ctxs(Ctx.UnboundExpr(cLamLike, usgs))
      CodeRes(cLamLike, isActuallyLambda, ctxs, usgs, env)
    }

    // For Assume, Assert, Require and Decreases
    def assumeLike(lab: Label.AssumeLike, pred: CodeRes, body: CodeRes)(using InLambda): CodeRes = {
//        val ctx = (u: Usages, c: Code) => {
//          val (u2, c2) = body.ctx(u, c)
//          val cAssms = codeOfSig(mkSig(pred.terminal, c2), codeTpe(c2))
//          // TODO: Added usgs ok?
//          val uPred = Usages.of(pred.terminal)(using pred.env)
//          pred.ctx(u2 ++ uPred, cAssms)
//        }
      // TODO: pred usgs ok?
      val ctxs = {
        if (pred.terminal == trueCode) pred.ctxs ++ body.ctxs
        else (pred.ctxs :+ Ctx.AssumeLike(lab, pred.terminal, Usages.of(pred.terminal)(using pred.env))) ++ body.ctxs
      }
      CodeRes(body.terminal, body.terminalHasLambdaDef, ctxs, body.usages, body.env)
    }

    // TODO: On pourrait faire mieux
    def ensuring(body: CodeRes, pred: CodeRes, tpe: Type)(using env: OEnv, inLambda: InLambda): CodeRes = {
      val (uBody, cBody) = body.selfPlugged
      val (uPred, cPred) = pred.selfPlugged
      val cEns = codeOfSig(mkEnsuring(cBody, cPred), tpe)
      // TODO: Ok?
//      val ctx = combinedUnboundCtx(cEns)(Seq(idCtx))(_ ++ uBody ++ uPred)
      val ctxs = Ctxs(Ctx.UnboundExpr(cEns, uBody ++ uPred))
      CodeRes(cEns, false, ctxs, Usages.empty, env)

//      // TODO: termHasLambdaDef?
//      // TODO: default env ok?
//      CodeRes.of(cEns, termHasLambdaDef = false)
    }

    def matchExpr(scrut: CodeRes, cases: Seq[CodeResMatchCase], tpe: Type)(using InLambda): CodeRes = {
      val cMatchExpr = codeOfSig(mkMatchExpr(scrut.terminal, cases.map(_.mc)), tpe)
      val hasLambda = scrut.terminalHasLambdaDef || cases.exists(_.hasLambdaDef)
      // TODO: Devrait-on aussi compter Usages of scrut?
      val usgsCases = cases.foldLeft(Usages.of(scrut.terminal)(using scrut.env))(_ ++ _.usages)
      val ctxs = scrut.ctxs :+ Ctx.Let(freshVarId("bdgMatch", codeTpe(cMatchExpr)), cMatchExpr, hasLambda, usgsCases, scrut.env, canSubst = true)
      CodeRes(cMatchExpr, hasLambda, ctxs, usgsCases, scrut.env)
//      val ctx = combinedBindingCtx(cMatchExpr, hasLamda)(Seq(scrut.ctx))(_ ++ usgsCases)(using scrut.env)
//      CodeRes(cMatchExpr, hasLamda, ctx, Usages.of(cMatchExpr)(using scrut.env) ++ usgsCases, scrut.env)
    }
  }

  /*
  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  def combinedBindingCtx(terminal: Code, terminalHasLam: Boolean)
                        (ctxs: Seq[(Usages, Code) => (Usages, Code)])
                        (incSubOccurrences: Usages => Usages)
                        (using env: OEnv, inLambda: InLambda)
                        (u: Usages, c: Code): (Usages, Code) = {
    assert(!isLambda(terminal), "woot?? On n'est pas sensé construire un lambda avec cette fn!!!")
    val terminalOcc = u(terminal)

    if (needsBinding(terminal, terminalHasLam, terminalOcc) == BindingCase.MustBind) {
      val bdg = idOfVariable(Variable.fresh("bdg", codeTpe(terminal)))
      val bound = codeOfSig(mkLet(bdg, terminal, c), codeTpe(c))
      val u2 = incSubOccurrences(u).setTo(terminal, Occurrence.Once(env, inLambda.v))
      foldCtxs(ctxs)(u2, bound)
    } else {
      val u2 = {
        if (terminalOcc.isZero) u
        else incSubOccurrences(u)
      }
      foldCtxs(ctxs)(u2, c)
    }
  }

  // TODO: Très mal nommé!!!
  def combinedUnboundCtx(terminal: Code)
                        (ctxs: Seq[(Usages, Code) => (Usages, Code)])
                        (incSubOccurrences: Usages => Usages)
                        (u: Usages, c: Code): (Usages, Code) = {
    val terminalOcc = u(terminal)
    val u2 = {
      if (terminalOcc.isZero) u
      else incSubOccurrences(u)
    }
    foldCtxs(ctxs)(u2, c)
  }

  def foldCtxs(ctxs: Seq[(Usages, Code) => (Usages, Code)])(u: Usages, c: Code): (Usages, Code) =
    ctxs.foldRight((u, c)) { case (ctx, (uAcc, cAcc)) => ctx(uAcc, cAcc) }
  */

  def sigOfExpr(e: Expr)(using env: OEnv, inLambda: InLambda): CodeRes = {
    val tpe = e.getType
    val res = e match {
      case v: Variable =>
        val vId = idOfVariable(v)
        val c = substByLet(vId).getOrElse(codeOfVarId(vId))
        // TODO: termHasLambdaDef ok??? et si v est une ref. à une lambda???
        CodeRes.of(c, termHasLambdaDef = false)

      case l: Literal[_] => CodeRes.of(codeOfSig(mkLit(l), tpe), false)

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val envThen = rcond.env.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using envThen)
        val envEls = rcond.env.withCond(negCodeOf(rcond.terminal)) // (using rcond.env)
        val rels = codeOfExpr(els)(using envEls)
        CodeRes.ifExpr(rcond, rthenn, rels, tpe)

      case e: (Lambda | Choose | Forall) =>
        val (body, isLambda, mkSig: (Code => Signature)) = e match {
          case Lambda(params, body) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (body, true, mkLambda(vParams, _))
          case Choose(res, pred) =>
            val vId = idOfVariable(res.toVariable)
            (pred, false, mkWickedChoose(vId, _))
          case Forall(params, pred) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (pred, false, mkForall(vParams, _))
        }
        val rbody = codeOfExpr(body)(using env, inLambda || isLambda)
        CodeRes.lambdaLike(rbody, tpe, isLambda)(mkSig)

      // TODO: Inline lambda si occ == 1
      case Let(vd, e, body) =>
        val vId = idOfVariable(vd.toVariable)
        val re = codeOfExpr(e)
        val canSubst = !isLambda(re.terminal)
        val rb = codeOfExpr(body)(using re.env.withLetBound(vId, re.terminal, canSubst))
        CodeRes.let(vId, re, rb, canSubst)

      case e: (Assume | Assert | Require | Decreases) =>
        val (lab: Label.AssumeLike, pred, body) = e match {
          case Assume(pred, body) => (Label.Assume, pred, body)
          case Assert(pred, _, body) => (Label.Assert, pred, body)
          case Require(pred, body) => (Label.Require, pred, body)
          case Decreases(measure, body) => (Label.Decreases, measure, body)
        }
        val rpred = codeOfExpr(pred)
        val bodyEnv = {
          if (lab != Label.Decreases) rpred.env.withCond(rpred.terminal)
          else rpred.env
        }
        val rbody = codeOfExpr(body)(using bodyEnv)
        CodeRes.assumeLike(lab, rpred, rbody)

      case Ensuring(body, pred) =>
        // TODO: Ok?
        val rbody = codeOfExpr(body)
        val rpred = codeOfExpr(pred) // Using the default env (not rbody.env)
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
      case or @ Or(_) =>
        codeOfDisjunction(unOr(or))

      case Not(e) =>
        // codeOfExprsBound(e, tpe)(mkNot)
        negExprOf(e)

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

      case Error(ofTpe, descr) =>
        CodeRes.of(codeOfSig(mkError(ofTpe, descr), tpe), false)
      case NoTree(ofTpe) =>
        CodeRes.of(codeOfSig(mkNoTree(ofTpe), tpe), false)

      // TODO: Passer en revue la pureté: p.ex. si on est pas exhaustif, devrait-on retourner "assumeChecked"?
      case MatchExpr(scrut, cases) =>
        // Ici, on fait qqchose de similaire au IfExpr
        val rscrut = codeOfExpr(scrut)
        val rcases = signatureOfCases(rscrut.terminal, scrut.getType, cases, Seq.empty)(using rscrut.env)
        CodeRes.matchExpr(rscrut, rcases, tpe)

      case e =>
        println("computeSignature: Do not know how to handle "+e)
        ???
    }
    simplifyTopLvl(res)
  }

  def signatureOfPatternExpr(subScrut: Code, scrutTpe: Type, pat: Pattern)(using env: OEnv, inLambda: InLambda): (LabelledPattern, Seq[(VarId, Code)], Seq[Code]) = {
    val vBinder = idOfVariable(pat.binder.getOrElse(ValDef.fresh("dummyBinder", scrutTpe)).toVariable)
    val bdgs1 = Seq((vBinder, subScrut))
    pat match {
      case WildcardPattern(_) => (LabelledPattern.Wildcard(subScrut), bdgs1, Seq.empty)

      case ADTPattern(_, id, tps, subps) =>
        val adt = ADTType(id, tps)
        val tcons = getConstructor(id, tps)
        assert(tcons.fields.size == subps.size)
        val conds1 = {
          if (isConstructor(subScrut, adt,id) == Some(true)) Seq.empty[Code]
          else Seq(codeOfSig(mkIsCtor(subScrut, adt, id), BoolTy))
        }
        val (labSubPats, bdgs2, conds2) = tcons.fields.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, conds1)) {
          // TODO: Annoté en dropvc?
          case ((labSubPatAcc, bdgsAcc, condsAcc), (fld, subpat)) =>
            val newScrut = codeOfSig(mkADTSelector(subScrut, adt, tcons, fld.id), fld.getType)
            // TODO: Env avec conds accumulées ok?
            val (labSubPat, newBdgs, newConds) = signatureOfPatternExpr(newScrut, fld.getType, subpat)(using env.withConds(condsAcc.toSet))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        (LabelledPattern.ADT(subScrut, id, tps, labSubPats), bdgs2, conds2)

      case TuplePattern(_, subps) =>
        val TupleType(bases) = scrutTpe
        assert(bases.size == subps.size)
        val (labSubPats, bdgs2, conds) = subps.zipWithIndex.foldLeft((Seq.empty[LabelledPattern], bdgs1, Seq.empty[Code])) {
          case ((labSubPatAcc, bdgsAcc, condsAcc), (subpat, i)) =>
            val newScrutTpe = bases(i)
            val newScrut = codeOfSig(mkTupleSelect(subScrut, i + 1), newScrutTpe)
            // TODO: Env avec conds accumulées ok?
            val (labSubPat, newBdgs, newConds) = signatureOfPatternExpr(newScrut, newScrutTpe, subpat)(using env.withConds(condsAcc.toSet))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        (LabelledPattern.TuplePattern(subScrut, labSubPats), bdgs2, conds)

      case LiteralPattern(_, lit) => (LabelledPattern.Lit(subScrut ,lit), bdgs1, Seq.empty)

      case UnapplyPattern(_, recs, id, tps, subps) =>
        // TODO: !!!! Si on utilise codeOf, ne pas oublier d'utiliser le subst approprié !!!
        sys.error(s"Does not know how to handle $pat")
    }
  }

  def signatureOfCase(cScrut: Code, scrutTpe: Type, mc: MatchCase)(using env: OEnv, inLambda: InLambda): (CodeResMatchCase, Seq[Code]) = {
    // patConds: sans le guard!
    val (labPat, bdgs, patConds) = signatureOfPatternExpr(cScrut, scrutTpe, mc.pattern)
    // TODO: Env bdgs ok????
    // TODO: Env bdgs ok????
    // TODO: Env bdgs ok????
    // TODO: Env bdgs ok????
    // TODO: Env bdgs ok????
    // TODO: Env bdgs ok????
    // TODO: canSubst?
    // TODO: !!! Si canSubst = false, il faudra faire un freshen d'identifiant p.ex. dans inlineLambda !!!
    val guardEnv = env.withLetBounds(bdgs, canSubst = true).withConds(patConds.toSet)
    // TODO: On pourrait conserver le ctx des guard pour le body? En gros, qu'on plug le body dans le ctx de guard

    // Comme pour les ifs, on ne hoist rien des branches

    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using guardEnv))
    val (usgsGuard, cGuard) = rguard.map(_.selfPlugged).getOrElse((Usages.empty, trueCode))

    val rhsEnv = guardEnv.withCond(cGuard)
    val rrhs = codeOfExpr(mc.rhs)(using rhsEnv)
    val (usgsRhs, rhs) = rrhs.selfPlugged

    val labMc = LabMatchCase(labPat, cGuard, rhs)
    (CodeResMatchCase(labMc, usgsGuard ++ usgsRhs, rrhs.terminalHasLambdaDef), patConds :+ cGuard)
  }

  def signatureOfCases(cScrut: Code, scrutTpe: Type, mcs: Seq[MatchCase], acc: Seq[CodeResMatchCase])
                      (using env: OEnv, inLambda: InLambda): Seq[CodeResMatchCase] = {
    if (mcs.isEmpty) acc
    else {
      val (newMatchCase, caseConds) = signatureOfCase(cScrut, scrutTpe, mcs.head)
      val negCaseConds = negatedConjunction(caseConds)
      signatureOfCases(cScrut, scrutTpe, mcs.tail, acc :+ newMatchCase)(using env.withCond(negCaseConds))
    }
  }

  def checkForContradiction(disj: Seq[Code])(using OEnv, InLambda): Boolean = {
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

  // TODO: Ok?
  def pDisj(e: Expr)(using OEnv): Seq[Code] = {
    ???
//    assert(e.getType == BoolTy, s"Got ${e.getType}")
//    sigOfExpr(e) match {
//      case Signature(Label.Or, children) => children // TODO: Flatten more?
//      case Signature(Label.Not, Seq(c)) => Seq(codeOfSig(pNegNormal(c), BoolTy)) // TODO: Ok?
//      case sig => Seq(codeOfSig(sig, BoolTy))
//    }
  }

  def codeOfDisjunction(disjs: Seq[Expr])(using env: OEnv, inLambda: InLambda): CodeRes = {
    assert(disjs.forall(_.getType == BoolTy))
    val (_, hasLamDef, usgs, cArgs) = disjs.foldLeft((env, false, Usages.empty, Seq.empty[Code])) {
      case ((env, hasLamDefAcc, usgsAcc, cArgsAcc), e) =>
        given OEnv = env
        val re = codeOfExpr(e)
        assert(codeTpe(re.terminal) == BoolTy, s"Got ${codeTpe(re.terminal)}")
        val (usgs, rePlugged) = re.selfPlugged
        val newEnv = re.env.withCond(negCodeOf(rePlugged))
        (newEnv, hasLamDefAcc || re.terminalHasLambdaDef, usgsAcc ++ usgs, cArgsAcc :+ rePlugged)
    }
    val isPure = cArgs.forall(c => codePurity(c).isPure)
    val cOr = simplifiedDisjunction(cArgs, mayDrop = isPure, mayReorder = isPure) // codeOfSig(mkOr(cArgs), tpe)
    /*
    // TODO: !!!! Voir s'il n'y a pas d'autre endroits susceptible à ce genre de choses !!!!
    // TODO: !!!! Voir s'il n'y a pas d'autre endroits susceptible à ce genre de choses !!!!
    // TODO: !!!! Voir s'il n'y a pas d'autre endroits susceptible à ce genre de choses !!!!
    code2sig(cOr) match {
      case Signature(Label.Let(v), Seq(e, body)) => ???
      case Signature(lab@(Label.Lambda(_) | Label.Choose(_) | Label.Forall(_)), Seq(pred, body)) => ???
      case Signature(Label.Ensuring, Seq(body, pred)) => ???
    }
    */
    unplugMap.get(cOr) match {
      // TODO: Voir commentaire MatchExpr
      // TODO: Voir commentaire MatchExpr
      // TODO: Voir commentaire MatchExpr
      // TODO: Voir commentaire MatchExpr
      // TODO: Voir commentaire MatchExpr
      case Some((cr, _)) => cr // TODO: Mais c'est dégueulasse !!!! Et c'est quoi la justification au juste?????
      case None =>
//        val ctx = combinedBindingCtx(cOr, hasLamDef)(Seq(idCtx))(_ ++ usgs)
        // Remarque: on retourne l'env original car les PCs des ors ne sont pas retenues hors des disjunctions.
        // P.ex. dans val x = b1 || b2 || b3 il serait insensé d'avoir !b1 && !b2 && !b3 dans le env de x.
        val ctxs = Ctxs(Ctx.Let(freshVarId("orBdg", BoolTy), cOr, hasLamDef, usgs, env, canSubst = true))
        CodeRes(cOr, hasLamDef, ctxs, usgs, env)
    }
  }

  // TODO: Voir si on peut pas faire qqchose pr eviter code dup avec pNegNormal
  // Signature de Not(child)
  def negExprOf(child: Expr)(using env: OEnv, inLambda: InLambda): CodeRes = {
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
        // TODO: terminalHasLambdaDef ok?
        rchild.derived(negCodeOf(rchild.terminal), newTermHasLambdaDef = false)
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

  def implied(rhs: Code)(using env: OEnv, inLambda: InLambda): Boolean = {
    if (env.conditions.isEmpty) rhs == trueCode
    else {
      // TODO: Quid pureté de rhs???
      // TODO: Pourrait-on envisager de cache env.condition?
      // a ==> b === a && b = a
      // TODO: Drop+Reorder ok?
      // TODO: Set to Seq ok?
      val lhsConj = conjunct(env.conditions.toSeq, mayDrop = true, mayReorder = true)
      val rhsLhsConj = conjunct(Seq(lhsConj, rhs), mayDrop = true, mayReorder = true)
      rhsLhsConj == lhsConj
    }
  }

  // Is `c` an ADT with constructor `id`?
  //   Some(true) - Yes
  //   Some(false) - No
  //   None - Can't tell
  def isConstructor(c: Code, adt: ADTType, id: Identifier)(using OEnv, InLambda): Option[Boolean] = {
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
  def varTpe(v: VarId): Type = varId2Var(v).tpe

  // TODO: Renommer, risque de confusion...
  def conjunct(conj: Seq[Code])(using OEnv, InLambda): Code = {
    val isPure = conj.forall(c => codePurity(c).isPure)
    conjunct(conj, isPure, isPure)
  }

  def conjunct(conj: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, InLambda): Code = negCodeOf(negatedConjunction(conj, mayDrop, mayReorder))

  def negatedConjunction(conj: Seq[Code], mayDrop: Boolean, mayReorder: Boolean)(using OEnv, InLambda): Code= simplifiedDisjunction(conj.map(negCodeOf), mayDrop, mayReorder)

  // TODO: Renommer, risque de confusion...
  def negatedConjunction(conj: Seq[Code])(using OEnv, InLambda): Code= {
    val isPure = conj.forall(c => codePurity(c).isPure)
    negatedConjunction(conj, isPure, isPure)
  }

  def codeOfIntLit(lit: BigInt, tpe: Type): Code = codeOfSig(mkLit(intLitOfType(lit, tpe)), tpe)

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

        def convertPattern(pat: LabelledPattern, vds: Map[Code, ValDef]): Pattern = {
          val bdg = vds.get(pat.scrut)
          pat match {
            case LabelledPattern.Wildcard(_) => WildcardPattern(bdg)
            case LabelledPattern.ADT(_, id, tps, sub) => ADTPattern(bdg, id, tps, sub.map(convertPattern(_, vds)))
            case LabelledPattern.TuplePattern(_, sub) => TuplePattern(bdg, sub.map(convertPattern(_, vds)))
            case LabelledPattern.Lit(_, lit) => LiteralPattern(bdg, lit)
            case LabelledPattern.Unapply(_, recs, id, tps, sub) => ???
          }
        }

        def uncodeOfCase(pat: LabelledPattern, cGuard: Code, cRhs: Code): (Pattern, RevRes, RevRes) = {
          val allPats = pat.allPatterns
          val scrutBdgs = allPats.zipWithIndex.map {
            case (pat, i) =>
              val vId = idOfVariable(Variable.fresh(s"bdg$i", codeTpe(pat.scrut)))
              vId -> pat.scrut
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
          (convertPattern(pat, scrutVds), guard, rhs)
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
        case None =>
          // TODO: Quid condition venant du simplifier (s'il y en as???)?
          // TODO: Différencier:
          //    -outer assms et local assms
          //    -outer open bound et local open bound
          given OEnv = OEnv.empty.copy(forceBinding = true)
          given InLambda = InLambda(false)
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val res = codePurity(codeOfExpr(getFunction(fn).fullBody).selfPlugged._2)
          visiting -= fn
          res match {
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

  // TODO: Ordre ok???
  // TODO: Ordre ok???
  // TODO: Ordre ok???
  def collectPatternConds(pat: LabelledPattern, recursive: Boolean)(using env: OEnv, inLambda: InLambda): Seq[Code] = pat match {
    case LabelledPattern.Wildcard(_) => Seq.empty
    case LabelledPattern.ADT(scrut, id, tps, subps) =>
      val adt = ADTType(id, tps)
      val tcons = getConstructor(id, tps)
      assert(tcons.fields.size == subps.size)
      val patConds = {
        if (isConstructor(scrut, adt, id) == Some(true)) Seq.empty[Code]
        else Seq(codeOfSig(mkIsCtor(scrut, adt, id), BoolTy))
      }
      val subconds = {
        // TODO: env with cond ok?
        if (recursive)
          subps.flatMap(collectPatternConds(_, true)(using env.withConds(patConds.toSet)))
        else Seq.empty
      }
      patConds ++ subconds
    case LabelledPattern.TuplePattern(_, subps) =>
      if (recursive) subps.flatMap(collectPatternConds(_, true))
      else Seq.empty
    case LabelledPattern.Lit(_, _) => Seq.empty
    case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
      sys.error(s"Does not know how to handle $pat")
  }

  def isLambda(c: Code): Boolean = code2sig(c) match {
    case Signature(Label.Lambda(_), _) => true
    case _ => false
  }

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
    val newScrut = replaceIn(pat.scrut, repl)
    pat match {
      case LabelledPattern.Wildcard(_) => LabelledPattern.Wildcard(newScrut)
      case LabelledPattern.ADT(_, id, tps, subps) =>
        LabelledPattern.ADT(newScrut, id, tps, subps.map(replaceIn(_, repl)))
      case LabelledPattern.TuplePattern(_, subps) =>
        LabelledPattern.TuplePattern(newScrut, subps.map(replaceIn(_, repl)))
      case LabelledPattern.Lit(_, lit) => LabelledPattern.Lit(newScrut, lit)
      case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
        sys.error(s"Does not know how to handle $pat")
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def codeOfVarId(v: VarId): Code = codeOfSig(mkVar(v), varTpe(v))

  private val sigPurity = new SigPurity

  def codePurity(c: Code)(using env: OEnv, inLambda: InLambda): Purity = sigPurity.codePurity(c)(using env.copy(forceBinding = true))
  def sigPurity(sig: Signature, tpe: Type)(using env: OEnv, inLambda: InLambda): Purity = sigPurity.sigPurity(sig, tpe)(using env.copy(forceBinding = true))

  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  def simplifyTopLvl(cr: CodeRes)(using InLambda): CodeRes = {
    given OEnv = cr.env
    val tpe = codeTpe(cr.terminal)
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)

    code2sig(cr.terminal) match {
      case Signature(Label.Assume | Label.Assert | Label.Require, Seq(pred, body)) =>
        sys.error("Quoi????")
//        if (pred == trueCode) {
//          val bodyUnpl = unplugMap(body) // TODO: Aucune garantie...
//          cr.derived(body)
//        } else cr

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
            if ((cond == trueCode && pEls.isPure) || thenn == els) {
              val (prevCtx, ifCtx) = cr.ctxs.popOrId
              assert(ifCtx match {
                case Ctx.Let(_, term, termHasLam, _, env, true) =>
                  term == cr.terminal && termHasLam == cr.terminalHasLambdaDef && env == cr.env
                case _ => false
              }, s"Trahison! Trahison! On a $ifCtx !!!")

              val thennUnpl = unplugMap(thenn)._1
              Some(CodeRes(thennUnpl.terminal, thennUnpl.terminalHasLambdaDef, prevCtx ++ thennUnpl.ctxs, Usages.empty, thennUnpl.env))
//              val ctx = foldCtxs(Seq(cr.ctx, thennUnpl.ctx))
//              Some(CodeRes(thennUnpl.terminal, thennUnpl.terminalHasLambdaDef, ctx, Usages.empty, thennUnpl.env))
            } else if (cond == falseCode && pThen.isPure) {
              val (prevCtx, ifCtx) = cr.ctxs.popOrId
              assert(ifCtx match {
                case Ctx.Let(_, term, termHasLam, _, env, true) =>
                  term == cr.terminal && termHasLam == cr.terminalHasLambdaDef && env == cr.env
                case _ => false
              }, s"Trahison! Trahison! On a $ifCtx !!!")

              val elsUnpl = unplugMap(els)._1
              Some(CodeRes(elsUnpl.terminal, elsUnpl.terminalHasLambdaDef, prevCtx ++ elsUnpl.ctxs, Usages.empty, elsUnpl.env))

//              val ctx = foldCtxs(Seq(cr.ctx, elsUnpl.ctx))
//              Some(CodeRes(elsUnpl.terminal, elsUnpl.terminalHasLambdaDef, ctx, Usages.empty, elsUnpl.env))
              // Some(cr.derived(els))
            } /*else if (thenn == els) {
              assert(pThen == pEls)
              Some(cr.derived(thenn))
            }*/
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
          case Signature(Label.ADT(id, _), args) =>
            assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
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
          case Some(base) => cr.derived(base)
          case None => cr
        }

      case Signature(Label.TupleSelect(ii), Seq(e)) =>
        val i = ii - 1
        code2sig(e) match {
          case Signature(Label.Tuple, args) => cr.derived(args(i))
          case _ => cr
        }

      // TODO: A revisiter une fois qu'on aura inlineLambda
      case Signature(Label.Application, callee +: args) =>
        code2sig(callee) match {
//          case Signature(Label.Lambda(params), Seq(body)) =>
//            assert(args.size == params.size)
//            val inlined = inlineLambda(params.zip(args), body)
//            code2sig(inlined)
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
        simplifyCases(cases) match {
          case SimplifiedCases.Empty => sys.error("ah bah là, je sais pas quoi faire...")
          case SimplifiedCases.ElidableMatchExpr(rhs) =>
            // TODO: Ok???
            val (prevCtx, matchCtx) = cr.ctxs.popOrId
            assert(matchCtx match {
              case Ctx.Let(_, term, termHasLam, _, env, true) =>
                term == cr.terminal && termHasLam == cr.terminalHasLambdaDef && env == cr.env
              case _ => false
            }, s"Trahison! Trahison! On a $matchCtx !!!")

            val rhsUnpl = unplugMap(rhs)._1
            CodeRes(rhsUnpl.terminal, rhsUnpl.terminalHasLambdaDef, prevCtx ++ rhsUnpl.ctxs, Usages.empty, rhsUnpl.env)

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

  def simplifyCase(matchCase: LabMatchCase)(using env: OEnv, inLambda: InLambda): SimplifiedCase = {
    val patConds = collectPatternConds(matchCase.pattern, recursive = true)
    val caseConds = patConds :+ matchCase.guard
    lazy val isRhsPure = codePurity(matchCase.rhs)(using env.withConds(caseConds.toSet)).isPure

    if (caseConds.forall(c => codePurity(c).isPure)) { // TODO: Calcul de la pureté imprécis, on devrait les accumuler...
      val caseCondsConj = conjunct(caseConds, mayDrop = true, mayReorder = true) // Puisque tout est pur
      if (caseCondsConj == trueCode) SimplifiedCase.Covered
      else if (caseCondsConj == falseCode && isRhsPure) SimplifiedCase.Unreachable
      else SimplifiedCase.Unchanged(caseConds)
//      given OEnv = env.withConds(caseConds.toSet)
//      if (implied(trueCode)) SimplifiedCase.Covered
//      else if (implied(falseCode) && codePurity(matchCase.rhs).isPure) SimplifiedCase.Unreachable
//      else SimplifiedCase.Unchanged(caseConds)
    } else SimplifiedCase.Unchanged(caseConds)
  }

  def simplifyCases(cases: Seq[LabMatchCase])(using OEnv, InLambda): SimplifiedCases = {
    def rec(cases: Seq[LabMatchCase], acc: Seq[LabMatchCase])(using env: OEnv): SimplifiedCases = {
      if (cases.isEmpty) {
        if (acc.isEmpty) SimplifiedCases.Empty
        else SimplifiedCases.Cases(acc)
      } else simplifyCase(cases.head) match {
        case SimplifiedCase.Unreachable => rec(cases.tail, acc)
        case SimplifiedCase.Covered =>
          if (acc.isEmpty) SimplifiedCases.ElidableMatchExpr(cases.head.rhs)
          else {
            val wildcard = LabMatchCase(LabelledPattern.Wildcard(cases.head.pattern.scrut), cases.head.guard, cases.head.rhs)
            SimplifiedCases.Cases(acc :+ wildcard)
          }
        case SimplifiedCase.Unchanged(caseConds) =>
          val negCaseConds = negatedConjunction(caseConds)
          rec(cases.tail, acc :+ cases.head)(using env.withCond(negCaseConds))
      }
    }
    rec(cases, Seq.empty)
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  def inlineLetBoundLambda(lam: VarId, in: Code)(using env: OEnv): Code = {
    val (cLam, _) = env.letDef.getOrElse(lam, sys.error("Treachery!!! Lambda not in env!!!"))
    val lamVarIdCode = codeOfVarId(lam)
    val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam)

    class InlineWrapperImpl extends CodeTransformer(depthLimit = None) {
      override type Extra = Unit

      // TODO: Ok par rapport à repl + let-bound canSubst truc?
      override def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Unit)(using env: OEnv): Signature = sig match {
        case Signature(Label.Application, `lamVarIdCode` +: args) =>
          assert(params.size == args.size)
          code2sig(inlineLambda(params.zip(args), body))
        case _ => super.transformImpl(sig, tpe, repl, ())
      }
    }

    (new InlineWrapperImpl).transformImpl(in, Map.empty, ())
  }

  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: remarque sur subst dans l'ordre (repr. l'inlining d'argument)
  def inlineLambda(argsSubst: Seq[(VarId, Code)], body: Code)(using env: OEnv): Code = {
    // Essentiellement un freshener + simplifyTopLvl a chaque step
    class InlinerImpl extends CodeTransformer(depthLimit = None) {
      override type Extra = Unit

      override def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Unit)(using env: OEnv): Signature = sig match {
        case Signature(Label.Let(v), Seq(e, b)) =>
          val re = transform(e, repl, ())
          val freshV = freshened(v)
          val newEnv = env.withLetBound(freshV, re, canSubst = !isLambda(re))
          val rb = transformImpl(b, repl + (codeOfVarId(v) -> codeOfVarId(freshV)), ())(using newEnv)
          simplifyTopLvl(mkLet(freshV, re, rb), tpe)

        case Signature(Label.Lambda(params), Seq(body)) =>
          val freshParams = params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }
          val rbody = transform(body, repl ++ freshParamsRepl, ())
          simplifyTopLvl(mkLambda(freshParams.map(_._2), rbody), tpe)

        case Signature(Label.Forall(params), Seq(pred)) =>
          val freshParams = params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }
          val rpred = transform(pred, repl ++ freshParamsRepl, ())
          simplifyTopLvl(mkForall(freshParams.map(_._2), rpred), tpe)

        case Signature(Label.Choose(v), Seq(pred)) =>
          val freshV = freshened(v)
          val rpred = transform(pred, repl + (codeOfVarId(v) -> codeOfVarId(freshV)), ())
          simplifyTopLvl(mkWickedChoose(freshV, rpred), tpe)

        // Remarque: pas de freshening à faire pour Match parce qu'il n'y a pas de binding à proprement parler

        case Signature(_, _) =>
          val rsig = super.transformImpl(sig, tpe, repl, ())
          simplifyTopLvl(rsig, tpe)
      }
    }

    // TODO: Remarque: inline une lambda peut donner lieu a une expr impure...
    // TODO: Pureté?
    val bodyTpe = codeTpe(body)
    val freshVars = argsSubst.map { case (v, _) => v -> freshened(v) }
    val freshVarsMap = freshVars.toMap
    val argsSubstMap = argsSubst.toMap
    // Bind the argument to fresh variables
    val initEnvBindings = freshVars.map {
      case (oldV, newV) => newV -> argsSubstMap(oldV)
    }
    val initEnv = env.withLetBounds(initEnvBindings)((_, c) => !isLambda(c))
    // Map to replace all occurrences of the old parameter with the fresh bindings variables.
    // TODO: Ok ça va se faire replace, mais ensuite??? Il n'y a pas la subst de letbind qui se fait!!!!
    //    -> Devrait être ok (CodeTransformer se charge)
    val initRepl = freshVars.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
    val inlined = (new InlinerImpl).transform(body, initRepl, ())(using initEnv)

    assert(codeTpe(inlined) == bodyTpe)
    argsSubst.foldRight(inlined) {
      case ((oldV, arg), rest) =>
        val newV = freshVarsMap(oldV)
        codeOfSig(mkLet(newV, arg, rest), bodyTpe)
    }
  }
  */

  def substByLet(v: VarId)(using env: OEnv): Option[Code] = env.letDef.get(v).filter(_._2).map(_._1)


  class SigPurity extends CodeTryFolder[Unit, Purity] {
    override type Extra = Unit

    private val visiting = mutable.Set.empty[Code]

    override def tryFoldImpl(sig: Signature, tpe: Type, acc: Purity, extra: Unit)(using env: OEnv, inLambda: InLambda): Either[Unit, Purity] = {
      val p = acc ++ codePurity(codeOfSig(sig, tpe)) // sigPurity(sig, tpe) // Remarque: ++ est lazy sur sa droite, donc si acc est impure, on ne va pas calculer sigPurityIn
      if (p == Impure) Left(())
      else Right(p)
    }

    // TODO: Caching
    // TODO: Ce truc avec les Delayed et les blocked by???
    def codePurity(c: Code)(using env: OEnv, inLambda: InLambda): Purity = {
      // TODO: On pourrait utiliser un "revLetDef" dans env
      if (env.letDef.exists(_._2._1 == c)) Pure
      else {
        if (visiting(c)) {
          println(s"!!! Already visited $c  =  ${code2sig(c)}")
        }
        visiting += c
        val purity = sigPurity(code2sig(c), codeTpe(c))
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
        purity
      }
    }

    def sigPurity(sig: Signature, tpe: Type)(using env: OEnv, inLambda: InLambda): Purity = sig match {
      case Signature(Label.Var(_) | Label.Lit(_), Seq()) => Pure
      case Signature(Label.Assume, Seq(pred, body)) =>
        if (pred == trueCode) codePurity(body) // pas besoin de env.withCond car de toute façon c'est true
        else Impure

      case Signature(Label.Assert, Seq(pred, body)) =>
        val pBody = codePurity(body)(using env.withCond(pred))
        if (pred == trueCode) pBody
        else assmChkPurity ++ pBody // Pureté comme Stainless

      case Signature(Label.Require, Seq(pred, body)) =>
        val pBody = codePurity(body)(using env.withCond(pred))
        if (pred == trueCode) pBody
        else assmChkPurity ++ pBody // Ditto

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        code2sig(pred) match {
          case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => codePurity(body)
          case _ => Impure
        }

      case Signature(Label.ADTSelector(adt, ctor, _), Seq(e)) =>
        // Remarque: on ne souhaite pas faire dépendre la pureté d'une sig en fn. de env!!!
        if (opts.assumeChecked || isConstructor(e, adt, ctor.id)/*(using OEnv.empty)*/ == Some(true)) codePurity(e)
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
        // TODO: Pureté ok? Après tout, un inline de lambda peut donner lieu à impure...
        assmChkPurity ++ fold(args.map(codePurity))

      case Signature(Label.Choose(v), Seq(pred)) =>
        if (pred == trueCode && hasInstance(varTpe(v)) == Some(true)) Pure
        else Impure

      // TODO: Pureté ok pour NoTree/Error? Car dans SWP et isImpure, aucune mention de NoTree/Error...
      case Signature(Label.Division | Label.Remainder | Label.Modulo | Label.NoTree(_) | Label.Error(_, _), _) =>
        assmChkPurity // TODO: Ok?

      // TODO: Pureté de Decreases?
      // TODO: Array select, map select, etc.???

      case sig => super.tryFoldImpl(sig, tpe, Pure, ()).getOrElse(Impure)
    }
  }

  private val hasLambdaDefInst = new HasLambdaDef

  def hasLambdaDefs(c: Code)(using OEnv, InLambda): Boolean = hasLambdaDefInst.hasLambdaDefs(code2sig(c), codeTpe(c))

  class HasLambdaDef extends CodeTryFolder[Unit, Unit] {
    override type Extra = Unit

    override def tryFoldImpl(sig: Signature, tpe: Type, acc: Unit, extra: Unit)
                            (using env: OEnv, inLambda: InLambda): Either[Unit, Unit] = {
      if (hasLambdaDefs(sig, tpe)) Left(())
      else Right(())
    }

    def hasLambdaDefs(sig: Signature, tpe: Type)(using OEnv, InLambda): Boolean = sig match {
      case Signature(Label.Lambda(_), Seq(_)) => true
      case sig => super.tryFoldImpl(sig, tpe, (), ()).isLeft
    }
  }

  /*
  // TODO: Commentaire à propos de code potentiel dans les labels qui ne sont pas transform
  class CodeTransformer {
    type Extra

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using env: OEnv, inLambda: InLambda): CodeRes = {
      repl.get(c) match {
        case Some(cc) =>
          assert(env.isBound(cc), "repl fait référence à un code qui n'est pas let-bound!!!")
          // Si cc est une var à un enclosing let, on le remplace par sa définition (pr autant que cela est permis)
          val res = code2sig(cc) match {
            case Signature(Label.Var(v), Seq()) => substByLet(v).getOrElse(cc)
            case _ => cc
          }
          CodeRes.of(res, termHasLambdaDef = false)
        case None =>
          transformImpl(code2sig(c), codeTpe(c), repl, extra)
      }
    }

    def canSubstLet(c: Code): Boolean = !isLambda(c)

    // TODO: revoir si tout est en ordre pour les ctx
    def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Extra)(using env: OEnv, inLambda: InLambda): CodeRes = sig match {
      case Signature(Label.Var(v), Seq()) =>
        val res = substByLet(v).getOrElse(codeOfVarId(v))
        // TODO: termHasLambdaDef ok??? et si v est une ref. à une lambda???
        CodeRes.of(res, termHasLambdaDef = false)

      case Signature(Label.Let(v), Seq(e, b)) =>
        val re = transform(e, repl, extra)
        val canSubst = canSubstLet(re.terminal)
        val rb = transform(b, repl + (e -> re.terminal), extra)(using env.withLetBound(v, re.terminal, canSubst))
        CodeRes.let(v, re, rb, canSubst)

      case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
        val rcond = transform(cond, repl, extra)
        val envThen = rcond.env.withCond(rcond.terminal)
        val rthenn = transform(thenn, repl, extra)(using envThen)
        val envEls = rcond.env.withCond(negCodeOf(rcond.terminal)) // (using rcond.env)
        val rels = transform(els, repl, extra)(using envEls)
        CodeRes.ifExpr(rcond, rthenn, rels, tpe)

      case Signature(lab@(Label.Lambda(_) | Label.Choose(_) | Label.Forall(_)), Seq(body)) =>
        val isLam = lab.isLambda
        val rbody = transform(body, repl, extra)(using env, inLambda || isLam)
        CodeRes.lambdaLike(rbody, tpe, isLam)(c => Signature(lab, Seq(c)))

      case Signature(lab@(Label.Assume | Label.Assert | Label.Require | Label.Decreases), Seq(pred, body)) =>
        val rpred = transform(pred, repl, extra)
        val bodyEnv = {
          if (lab.isDecreases) rpred.env
          else rpred.env.withCond(rpred.terminal)
        }
        val rbody = transform(body, repl, extra)(using bodyEnv)
        CodeRes.assumeLike(rpred, rbody)((p, b) => Signature(lab, Seq(p, b)))

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        // TODO: Ok?
        val rbody = transform(body, repl, extra)
        val rpred = transform(pred, repl, extra)
        CodeRes.ensuring(rbody, rpred, tpe)

      case Signature(Label.Or, disjs) =>
        val (_, hasLamDef, usgs, rdisjs) = unOrCodes(disjs).foldLeft((env, false, Usages.empty, Seq.empty[Code])) {
          case ((env, hasLamDefAcc, usgsAcc, rdisjsAcc), disj) =>
            given OEnv = env
            val rdisj = transform(disj, repl, extra)
            val (usgs, rdisjPlugged) = rdisj.selfPlugged
            val newEnv = rdisj.env.withCond(negCodeOf(rdisjPlugged))
            (newEnv, hasLamDefAcc || rdisj.terminalHasLambdaDef, usgsAcc ++ usgs, rdisjsAcc :+ rdisjPlugged)
        }
        // TODO: Faire comme codeOfDisj
        val cOr = codeOfSig(mkOr(unOrCodes(rdisjs)), tpe)
        val ctx = combinedBindingCtx(cOr, hasLamDef)(Seq(idCtx))(_ ++ usgs)
        CodeRes(cOr, hasLamDef, ctx, usgs ++ Usages.of(cOr), env)

      case Signature(Label.Lit(_) | Label.Error(_, _) | Label.NoTree(_), Seq()) =>
        CodeRes.of(codeOfSig(sig, tpe), false)

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val cases = pats.zip(guards).zip(rhss).map {
          case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
        }
        val rscrut = transform(scrut, repl, extra)
        // TODO: Voir si repl ok
        // TODO: Voir si repl ok
        // TODO: Voir si repl ok
        val rcases = transformCases(cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using rscrut.env)
        CodeRes.matchExpr(rscrut, rcases, tpe)

      // TODO: Que pour les cas triviaux où env est le même, bindings std, etc.
      case Signature(lab, children) =>
        transformSeq(children, tpe, repl, extra)(Signature(lab, _))
    }

    final def transformSeq(cs: Seq[Code], tpe: Type, repl: Map[Code, Code], extra: Extra)(mkSig: Seq[Code] => Signature)(using env: OEnv, inLambda: InLambda): CodeRes = {
      given x_x: OEnv = sys.error("Carefully select env")
      val (newEnv, ress) = cs.foldLeft((env, Seq.empty[CodeRes])) {
        case ((env, codeResAcc), c) =>
          val res = transform(c, repl, extra)(using env)
          (res.env, codeResAcc :+ res)
      }
      combineCodeRes(ress, tpe)(mkSig)(using newEnv)
    }

    def transformCase(matchCase: LabMatchCase, repl: Map[Code, Code], extra: Extra)(using env: OEnv, inLambda: InLambda): (CodeResMatchCase, Seq[Code]) = {
      // TODO: Voir si repl ok
      // TODO: Voir si repl ok
      // TODO: Voir si repl ok
      val newPat = replaceIn(matchCase.pattern, repl)
      val patConds = collectPatternConds(newPat, recursive = true)
      // TODO: Env pas de bdgs ok????
      // TODO: Env pas de bdgs ok????
      // TODO: Env pas de bdgs ok????
      // TODO: Env pas de bdgs ok????
      val rguard = transform(matchCase.guard, repl, extra)(using env.withConds(patConds.toSet))
      val (usgsGuard, cGuard) = rguard.selfPlugged
      val caseConds = patConds :+ cGuard
      val rrhs = transform(matchCase.rhs, repl, extra)(using env.withConds(caseConds.toSet))
      val (usgsRhs, cRhs) = rrhs.selfPlugged
      (CodeResMatchCase(LabMatchCase(newPat, cGuard, cRhs), usgsGuard ++ usgsRhs, rrhs.terminalHasLambdaDef), caseConds)
    }

    def transformCases(cases: Seq[LabMatchCase], repl: Map[Code, Code], extra: Extra,
                       acc: Seq[CodeResMatchCase])
                      (using env: OEnv, inLambda: InLambda): Seq[CodeResMatchCase] = {
      if (cases.isEmpty) acc
      else {
        val (newMatchCase, caseConds) = transformCase(cases.head, repl, extra)
        val negCaseConds = negatedConjunction(caseConds)
        transformCases(cases.tail, repl, extra, acc :+ newMatchCase)(using env.withCond(negCaseConds))
      }
    }
  }
  */

  class CodeTryFolder[E, T](val depthLimit: Option[Int] = None) {
    type Extra
    var currDepthLimit = depthLimit
    var depth = 0

    final def tryFold(sig: Signature, tpe: Type, acc: T, extra: Extra)(using OEnv, InLambda): Either[E, T] = {
      if (currDepthLimit.exists(_ <= depth)) limitDepthReached(sig, tpe, acc, extra)
      else {
        depth += 1
        val res = tryFoldImpl(sig, tpe, acc, extra)
        depth -= 1
        res
      }
    }

    final def tryFold(c: Code, acc: T, extra: Extra)(using OEnv, InLambda): Either[E, T] = tryFold(code2sig(c), codeTpe(c), acc, extra)

    def limitDepthReached(sig: Signature, tpe: Type, acc: T, extra: Extra)(using OEnv, InLambda): Either[E, T] = Right(acc)

    def canSubstLet(c: Code): Boolean = !isLambda(c)

    def tryFoldImpl(sig: Signature, tpe: Type, acc: T, extra: Extra)(using env: OEnv, inLambda: InLambda): Either[E, T] = sig match {
      // TODO: Quid subst des let???? --> mettre un case ici pr les var
      //    -> ça sert à rien non? De toute façon, on suppose qu'on utilise déjà les defs non???

      case Signature(Label.Var(v), Seq()) =>
        substByLet(v).map(tryFold(_, acc, extra)).getOrElse(Right(acc))

      case Signature(Label.Let(v), Seq(e, b)) =>
        for {
          re <- tryFold(e, acc, extra)
          rb <- tryFold(b, re, extra)(using env.withLetBound(v, e, canSubst = canSubstLet(e)))
        } yield rb

      case Signature(Label.Assert | Label.Assume | Label.Require, Seq(pred, body)) =>
        for {
          rpred <- tryFold(pred, acc, extra)
          rbody <- tryFold(body, rpred, extra)(using env.withCond(pred))
        } yield rbody

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        for {
          rcond <- tryFold(cond, acc, extra)
          rthn <- tryFold(thn, rcond, extra)(using env.withCond(cond))
          rels <- tryFold(els, rthn, extra)(using env.withCond(negCodeOf(cond)))
        } yield rels

      case Signature(Label.Or, args) =>
        tryFoldSeq(args, acc, extra) { case (disj, env) => env.withCond(negCodeOf(disj)) /*(using env)*/ }

      case Signature(Label.Lambda(_), Seq(body)) => tryFold(body, acc, extra)(using env, InLambda(true))

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val rscrut = tryFold(scrut, acc, extra)
        pats.zip(guards).zip(rhss).foldLeft(rscrut.map((_, env))) {
          case (Right((acc, env)), ((pat, guard), rhs)) =>
            val patConds = collectPatternConds(pat, recursive = true)
            for {
              rpat <- tryFoldSeq(patConds, acc, extra)
              rguard <- tryFold(guard, rpat, extra)(using env.withConds(patConds.toSet))
              caseConds = patConds :+ guard
              rrhs <- tryFold(rhs, rguard, extra)(using env.withConds(caseConds.toSet))
              negCaseConds = negatedConjunction(caseConds)
            } yield (rrhs, env.withCond(negCaseConds))
          case (Left(e), _) => Left(e)
        }.map(_._1)

      // TODO: Suppose que lab pas besoin d'avoir des sous parties transformées. P.ex. pour MatchExpr, cela ne jouera pas (en raison des recs?)
      case Signature(_, children) => tryFoldSeq(children, acc, extra)
    }

    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(using OEnv, InLambda): Either[E, T] =
      tryFoldSeq(cs, acc, extra)((_, env) => env)

    // TODO: Dire que le nextEnv est appliqué pour le suivant (et pas pr le "current")
    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(nextEnv: (Code, OEnv) => OEnv)(using env: OEnv, inLambda: InLambda): Either[E, T] = {
      cs.foldLeft(Right((acc, env)): Either[E, (T, OEnv)]) {
        case (Right((acc, env)), c) =>
          tryFold(c, acc, extra).map((_, nextEnv(c, env)))
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