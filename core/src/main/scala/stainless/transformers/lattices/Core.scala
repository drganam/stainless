package stainless
package transformers
package lattices

import inox.solvers

trait Core extends Definitions { ocbsl =>
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable // A bit ironic that we import mutable stuff right after "Purity"...

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


  private val pluggedMap = mutable.Map.empty[(CodeRes, Ctxs, Env), (Occurrences, Code)]
  private val unplugMap = mutable.Map.empty[(Code, Env), Map[Ctxs, (CodeRes, Occurrences)]]

  private val sig2codeMap = mutable.Map.empty[Signature, Code]
  private val code2sigMap = mutable.Map.empty[Code, Signature]
  private val codeTpeMap = mutable.Map.empty[Code, Type]

  private var varIdCounter: Int = 0
  private val varId2Var = mutable.Map.empty[VarId, Variable]
  private val var2VarId = mutable.Map.empty[Variable, VarId]

  private val codePurityInst = new CodePurity

  // Not for sparing allocations, but for sparing key strokes :p
  final val BoolTy: Type = BooleanType()

  final val falseSig: Signature = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
  final val trueSig: Signature = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
  final val unitSig: Signature = Signature(Label.Lit(UnitLiteral()), Seq.empty)
  final val falseCode: Code = codeOfSig(falseSig, BoolTy)
  final val trueCode: Code = codeOfSig(trueSig, BoolTy)
  final val unitCode: Code = codeOfSig(unitSig, UnitType())

  final inline val debug = true

  final inline def assert(cond: => Boolean): Unit =
    inline if (debug) Predef.assert(cond)

  final inline def assert(cond: => Boolean, msg: => String): Unit =
    inline if (debug) Predef.assert(cond, msg)

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Various simple ADTs

  case class Env(nesting: LambdaNesting, forceBinding: Boolean) {
    def inc: Env = Env(nesting.inc, forceBinding)
    def incIf(lab: Label.LambdaLike): Env = Env(nesting.incIf(lab), forceBinding)
  }

  object Env {
    def empty: Env = Env(LambdaNesting(0), false)
  }

  case class LambdaNesting(level: Int) {
    require(level >= 0)

    def inAnyLambda: Boolean = level > 0
    def inc: LambdaNesting = LambdaNesting(level + 1)
    def incIf(lab: Label.LambdaLike): LambdaNesting =
      if (lab.isLambda) inc else this
  }

  enum OccurrenceKind {
    case Expanded
    case Applied
  }

  enum Occurrence {
    case Zero
    case Once(inCtxs: Ctxs, nesting: LambdaNesting, kind: OccurrenceKind)
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
      case Once(_, _, _) => true
      case _ => false
    }

    def isMany: Boolean = this match {
      case Many => true
      case _ => false
    }

    def nonZero: Boolean = !isZero

    override def toString: String = this match {
      case Zero => "Zero"
      case Once(_, _, _) => "Once"
      case Many => "Many"
    }
  }

  case class Occurrences(c2u: Map[Code, Occurrence]) {
    def hasLambda: Boolean = c2u.keys.exists(isLambda)

    def apply(c: Code): Occurrence = c2u.getOrElse(c, Occurrence.Zero)

    def +(c: Code, occ: Occurrence): Occurrences = this ++ Occurrences(Map(c -> occ))

    def ++(that: Occurrences): Occurrences = Occurrences((c2u.keySet ++ that.c2u.keySet)
      .map(c => c -> (this (c) ++ that(c))).toMap)

    def setTo(c: Code, o: Occurrence): Occurrences = Occurrences(c2u + (c -> o))

    def -(c: Code): Occurrences = Occurrences(c2u - c)

    // TODO: What is this name!!!!
    def manyied: Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Zero) => (c, Occurrence.Zero) // TODO: Should we just filter these out?
      case (c, _) => c -> Occurrence.Many
    })

    def allSuffixes(ctxs: Ctxs): Boolean = c2u.values.forall {
      case Occurrence.Once(inCtxs, _, _) => ctxs.isPrefixOf(inCtxs)
      case _ => true
    }
  }

  object Occurrences {
    def empty: Occurrences = Occurrences(Map.empty)

    def of(c: Code)(using env: Env, ctxs: Ctxs): Occurrences = {
      if (isLit(c)) Occurrences.empty
      else {
        val impures = ctxs.impureParts
        Occurrences(Map(c -> Occurrence.Once(impures, env.nesting, OccurrenceKind.Expanded)))
      }
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
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Ctxs and CodeRes

  enum Ctx {
    case BoundDef(terminal: Code)
    case AssumeLike(lab: Label.AssumeLike, predTerminal: Code)
    case Assumed(cond: Code) // TODO: Dire que c'est p.ex. apres if (cond), où le assume(cond) ds la branche n'est pas nécessaire (car impliqué)

    lazy val hc: Int = this match {
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

    private val impurePartsCache = mutable.Map.empty[Env, Ctxs]

    def impureParts(using env: Env): Ctxs = {
      if (env.forceBinding) return this

      impurePartsCache.getOrElseUpdate(env, {
        Ctxs(ctxs.foldLeft((Seq.empty[Ctx], Seq.empty[Ctx])) {
          case ((prevCtxs, impureCtxs), assm@(Ctx.Assumed(_) | Ctx.AssumeLike(_, _))) => (prevCtxs :+ assm, impureCtxs :+ assm)
          case ((prevCtxs, impureCtxs), b@Ctx.BoundDef(t)) =>
            val p = codePurity(t)(using env, Ctxs(prevCtxs))
            if (p.isPure) (prevCtxs :+ b, impureCtxs)
            else (prevCtxs :+ b, impureCtxs :+ b)
        }._2)
      })
    }

    def withReplacedPrefix(oldPrefix: Ctxs, newPrefix: Ctxs): Ctxs = {
      assert(oldPrefix.isPrefixOf(this))
      val suffix = ctxs.drop(oldPrefix.size)
      suffix.foldLeft(newPrefix)(_.addCtx(_))
    }

    def addCtx(ctx: Ctx): Ctxs = ctx match {
      case bd@Ctx.BoundDef(t) =>
        if (isLitVarOrBoundDef(t)) this
        else Ctxs(ctxs :+ bd)
      case a@Ctx.Assumed(cond) =>
        if (cond == trueCode || allCondsSet.contains(cond)) this
        else Ctxs(ctxs :+ a)
      case a@Ctx.AssumeLike(kind, pred) =>
        if (pred == trueCode || (!kind.isDecreases && allCondsSet.contains(pred))) this
        else Ctxs(ctxs :+ a)
    }

    def size: Int = ctxs.size

    def lastOption: Option[Ctx] = ctxs.lastOption

    def pop: Option[(Ctxs, Ctx)] = {
      if (ctxs.isEmpty) None
      else Some((Ctxs(ctxs.init), ctxs.last))
    }

    // En gros: On plug jusqu'à ce que l'on atteigne inCtxs
    def plugged(inCtxs: Ctxs, u: Occurrences, c: Code)(using env: Env): (Occurrences, Code, Set[Code]) = {
      assert(inCtxs.isPrefixOf(this))

      def rec(curr: Ctxs, u: Occurrences, c: Code, inlinedLet: Set[Code]): (Occurrences, Code, Set[Code]) = {
        assert(inCtxs.isPrefixOf(curr))
        assert(curr.isPrefixOf(this))
        if (curr.ctxs.size == inCtxs.ctxs.size) (u, c, inlinedLet)
        else {
          assert(curr.ctxs.nonEmpty)
          val (prev, toPlug) = curr.pop.get
          val (u2, c2, inlinedLet2) = Ctxs.plugCtx(curr, prev, toPlug, u, c, inlinedLet)
          val res = rec(prev, u2, c2, inlinedLet2)
          val noTailRecPls = Ctxs(curr.ctxs)
          res
        }
      }

      rec(this, u, c, Set.empty)
    }

    def isBoundDef(c: Code): Boolean = ctxs.exists(_.isBoundDef(c))

    def takeUntilDefined(c: Code): Ctxs = {
      Ctxs(ctxs.takeWhile {
        case Ctx.BoundDef(c2) => c != c2
        case _ => true
      })
    }

    def isLitVarOrBoundDef(c: Code): Boolean = isLitOrVar(c) || isBoundDef(c)

    def isPrefixOf(that: Ctxs): Boolean = ocbsl.isPrefixOf(this.ctxs, that.ctxs)

    // TODO: Hmm, en fait, c'est p-e mieux si on fait la computation dans plugCtx
    // TODO: Yeet composition et isPure de Ctx.BoundDef
    def addBoundDef(df: Code)(using env: Env): Ctxs = {
      assert(CodeRes.isTerminal(df))
      if (isLitOrVar(df) || isBoundDef(df)) this
      else {
        Ctxs(ctxs :+ Ctx.BoundDef(df))
      }
    }

    def withCond(cond: Code): Ctxs = {
      if (cond == trueCode || allCondsSet.contains(cond)) this
      else Ctxs(ctxs :+ Ctx.Assumed(cond))
    }

    def withNegatedCond(cond: Code): Ctxs = withCond(negCodeOf(cond))

    def withConds(conds: Seq[Code]): Ctxs =
      conds.foldLeft(this)((acc, c) => acc.withCond(c))

    def withAssumeLike(kind: Label.AssumeLike, pred: Code): Ctxs = {
      assert(CodeRes.isTerminal(pred))
      assert(isLitVarOrBoundDef(pred))
      if (pred == trueCode || (!kind.isDecreases && allCondsSet.contains(pred))) this
      else Ctxs(ctxs :+ Ctx.AssumeLike(kind, pred))
    }
  }

  object Ctxs {
    // private val plugCtxsMap = mutable.Map.empty[(Ctxs, Occurrences, Code, OEnv), (Occurrences, Code, Set[Code])]

    def empty: Ctxs = new Ctxs(Seq.empty)

    private def plugCtx(curr: Ctxs, prev: Ctxs, toPlug: Ctx, u: Occurrences, c: Code, inlinedLet: Set[Code])
                       (using env: Env): (Occurrences, Code, Set[Code]) = {
      if (Thread.interrupted()) throw new InterruptedException("Oh non :(")

      /*
      plugCtxsMap.get((curr, u, c, env)) match {
        case Some(r) => return r
        case None => ()
      }
      */
      // TODO: Quid si inline dans un lambda mais pas ailleurs "plus loin"???
      // TODO: Cette histoire de assume(...) en début de lambda????
      // TODO: Dire qu'ici et pas ailleurs car on ne veut pas remettre des ctxs.addBoundDef pr les lambdas
      def inlineAppliedLambda(cLam: Code, in: Code): (Occurrences, Code, Set[Code]) = {
        val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam)
        object inliner extends CodeTransformer {
          override type Extra = Unit

          // TODO: Test inline lambda dans lambda?
          override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)
                                    (using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
            case Signature(Label.Application, `cLam` +: args) =>
              assert(params.size == args.size)
              inlineLambda(ctxs, params.zip(args), body)
            case _ => super.transformImpl(c, repl, ())
          }
        }

        val inlined = inliner.transform(in, Map.empty, ())(using env, prev)
        assert(prev.isPrefixOf(inlined.ctxs))
        val inlinedOcc = occurrencesOf(inlined.terminal)(using env, inlined.ctxs)
        val (u, c, inlined2) = inlined.ctxs.plugged(prev, inlinedOcc, inlined.terminal)
        (u, c, inlined2 + cLam)
      }

      assert(curr.ctxs == prev.ctxs :+ toPlug)
      assert(u.allSuffixes(curr.impureParts))
      /*
      val uuu0 = occurrencesOf(c)(using env, curr)
      val uuu = uuu0.withRemovedBindings(inlinedLet)
      if (u != uuu) {
        val eq = u.c2u.toSet.intersect(uuu.c2u.toSet)
        val diff = (u.c2u.toSet ++ uuu.c2u.toSet) -- eq
        assert(false, "!!! Pas d'égalité")
      }
      */

      val (u2, c2, inlinedLet2) = toPlug match {
        case Ctx.Assumed(_) => (u, c, inlinedLet)

        case Ctx.BoundDef(terminal) =>
          assert(CodeRes.isTerminal(terminal))
          assert(!isLitOrVar(terminal))
          val composition = occurrencesOf(terminal)(using env, prev) // La composition comprend le terminal
          assert(composition(terminal).isOnce)
          val compWoTerm = composition - terminal
          val definitionOccurrence = u(terminal)
          val bdgCase = needsBinding(terminal, compWoTerm, u, inlinedLet)(using env, prev)

          (bdgCase, definitionOccurrence) match {
            case (BindingCase.MustBind, _) =>
              val cLet = codeOfSig(mkLet(terminal, c), codeTpe(c))
              val u2 = compWoTerm ++ u.setTo(terminal, Occurrence.Once(prev.impureParts, env.nesting, OccurrenceKind.Expanded))
              (u2, cLet, inlinedLet)
            case (BindingCase.Inlinable, Occurrence.Once(_, _, OccurrenceKind.Applied)) if isLambda(terminal) =>
              inlineAppliedLambda(terminal, c)
            case _ =>
              val u2 = definitionOccurrence match {
                case Occurrence.Zero => u
                case Occurrence.Once(_, _, _) =>
                  u ++ compWoTerm
                case Occurrence.Many =>
                  // Ce cas se passe pour les x.f1.fnField où l'on les inline au lieu de les bind
                  u ++ compWoTerm.manyied
              }
              (u2, c, inlinedLet + terminal)
          }

        case Ctx.AssumeLike(lab, predTerminal) =>
          assert(CodeRes.isTerminal(predTerminal))
          assert(prev.isLitVarOrBoundDef(predTerminal))
          val c2 = codeOfSig(mkAssumeLike(lab, predTerminal, c), codeTpe(c))
          (u ++ occurrencesOf(predTerminal)(using env, prev), c2, inlinedLet)
      }

      assert(u2.allSuffixes(prev.impureParts))
      /*
      val uuu20 = occurrencesOf(c2)(using env, prev)
      val uuu2 = uuu20.withRemovedBindings(inlinedLet2)
      if (u2 != uuu2) {
        val eq = u2.c2u.toSet.intersect(uuu2.c2u.toSet)
        val diff = (u2.c2u.toSet ++ uuu2.c2u.toSet) -- eq
        assert(false, "!!! Pas d'égalité2")
      }
      */

      // plugCtxsMap += (curr, u, c, env) -> (u2, c2, inlinedLet2)

      (u2, c2, inlinedLet2)
    }
  }

  private val pluggedOccMap = mutable.Map.empty[(Env, Code), mutable.Map[Ctxs, Occurrences]]

  case class CodeRes(terminal: Code, ctxs: Ctxs) {
    assert(CodeRes.isTerminal(terminal), s"Gag: $terminal n'est pas un terminal (est un ${code2sig(terminal)})")

    lazy val hc: Int = java.util.Objects.hash(terminal, ctxs)
    override def hashCode(): Int = hc

    def selfPlugged(inCtxs: Ctxs)(using env: Env): (Occurrences, Code) = {
      assert(inCtxs.isPrefixOf(ctxs))
      pluggedMap.getOrElseUpdate((this, inCtxs, env), {
        val u = occurrencesOf(terminal)(using env, ctxs)
        val (u2, c, inlinedLet) = ctxs.plugged(inCtxs, u, terminal)
        /*
        val expected0 = occurrencesOf(c)(using env, inCtxs)
        val expected = expected0.withRemovedBindings(inlinedLet)
        if (expected != u2) {
          val eq = u2.c2u.toSet.intersect(expected.c2u.toSet)
          val diff = (u2.c2u.toSet ++ expected.c2u.toSet) -- eq
          // if (!env.forceBinding)
          assert(false, "owie, not the same :(")
        }
        */
        assert(codeTpe(terminal) == codeTpe(c), s"${codeTpe(terminal)} != ${codeTpe(c)}")
        locally {
          val currEntry = unplugMap.getOrElse((c, env), Map.empty)
          // TODO: Voir si oui ou non c'est ok
          // assert(!currEntry.contains(inCtxs))
          val newEntry = currEntry + (inCtxs -> (this, u2))
          unplugMap += (c, env) -> newEntry
        }
        locally {
          val currEntry = pluggedOccMap.getOrElseUpdate((env, c), mutable.Map.empty)
          val got = currEntry.get(inCtxs).map { expected =>
            val eq = u2.c2u.toSet.intersect(expected.c2u.toSet)
            val diff = (u2.c2u.toSet ++ expected.c2u.toSet) -- eq
            (expected, eq, diff)
          }
//          val thirdOne = occurrencesOf(c)(using env, inCtxs)
//          val eq = u2.c2u.toSet.intersect(thirdOne.c2u.toSet)
//          val diff = (u2.c2u.toSet ++ thirdOne.c2u.toSet) -- eq
          assert(got.forall(_._1 == u2))
//          assert(currEntry.get(inCtxs.impureParts).forall(_ == u2))

//          val got = currEntry.toSeq.map { case (inCtxs2, occ2) =>
//            val got = occ2.withReplacedPrefix(inCtxs2, inCtxs.impureParts)
//            val eq = u2.c2u.toSet.intersect(got.c2u.toSet)
//            val diff = (u2.c2u.toSet ++ got.c2u.toSet) -- eq
//            (got, eq, diff)
//          }
//          assert(got.forall(_._1 == u2))
          currEntry += inCtxs -> u2
        }
        (u2, c)
      })
    }

    def derived(newTerminal: Code)(using env: Env): CodeRes =
      CodeRes(newTerminal, ctxs.addBoundDef(newTerminal))
  }

  object CodeRes {
    def isTerminal(c: Code): Boolean = code2sig(c) match {
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Decreases | Label.Let, _) => false
      case _ => true
    }

    def ifExpr(cond: CodeRes, thenn: CodeRes, els: CodeRes, tpe: Type)(using env: Env): CodeRes = {
      assert(cond.ctxs.isPrefixOf(thenn.ctxs))
      assert(cond.ctxs.isPrefixOf(els.ctxs))
      val (compThenn, cThenn) = thenn.selfPlugged(cond.ctxs.withCond(cond.terminal))
      val (compEls, cEls) = els.selfPlugged(cond.ctxs.withNegatedCond(cond.terminal))
      val terminal = codeOfSig(mkIfExpr(cond.terminal, cThenn, cEls), tpe)
//      val compIf = cond.composition ++ compThenn ++ compEls ++ Occurrences.of(terminal)(using env, cond.ctxs)
      CodeRes(terminal, cond.ctxs.addBoundDef(terminal))
    }

    // For Lambda, Choose and Forall
    def lambdaLike(lab: Label.LambdaLike, body: CodeRes, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(body.ctxs))
      val (compBody, cBody) = body.selfPlugged(ctxs)(using env.incIf(lab))
      val terminal = codeOfSig(mkLambdaLike(lab, cBody), tpe)
//      val compLambda = compBody ++ Occurrences.of(terminal)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    // TODO: On pourrait faire mieux (p.ex. extraire des trucs communs ds body pr en faire beneficier pred)
    def ensuring(body: CodeRes, pred: CodeRes, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(pred.ctxs))
      assert(ctxs.isPrefixOf(body.ctxs))
      val (compBody, cBody) = body.selfPlugged(ctxs)
      val (compPred, cPred) = pred.selfPlugged(ctxs)
      val terminal = code2sig(cPred) match {
        case Signature(Label.Lambda(_), Seq(`trueCode`)) => cBody
        case _ => codeOfSig(mkEnsuring(cBody, cPred), tpe)
      }
//      val compEnsuring = compBody ++ compPred ++ Occurrences.of(terminal)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def matchExpr(scrut: CodeRes, cases: Seq[CodeResMatchCase], tpe: Type)(using env: Env): CodeRes = {
      assert(cases.nonEmpty)
      val terminal = codeOfSig(mkMatchExpr(scrut.terminal, cases.map(_.mc)), tpe)
//      val compMatch = cases.foldLeft(scrut.composition)(_ ++ _.composition) ++ Occurrences.of(terminal)(using env, scrut.ctxs)
      CodeRes(terminal, scrut.ctxs.addBoundDef(terminal))
    }

    def err(ofTpe: Type, descr: String, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkError(ofTpe, descr), tpe)
//      val comp = Occurrences.of(terminal)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def noTree(ofTpe: Type, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkNoTree(ofTpe), tpe)
//      val comp = Occurrences.of(terminal)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }
  }

  final def combineCodeRes(codeRess: Seq[CodeRes], tpe: Type)(cons: Seq[Code] => Signature)(using Env, Ctxs): CodeRes =
    combineCodeRes(codeRess)(cs => codeOfSig(cons(cs), tpe))

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  final def combineCodeRes(codeRess: Seq[CodeRes])(cons: Seq[Code] => Code)(using env: Env, ctxs: Ctxs): CodeRes = {
    assert(codeRess.isEmpty || (ctxs eq codeRess.last.ctxs))
    assert(codeRess.forall(_.ctxs.isPrefixOf(ctxs)))
    assert(codeRess.size <= 1 || codeRess.zip(codeRess.tail).forall { case (prev, cur) => prev.ctxs.isPrefixOf(cur.ctxs) })

    val terminal = cons(codeRess.map(_.terminal))
    // TODO: Etendre ce check à d'autre cas (ensuring, etc.)
    assert(!isLambdaLike(terminal))
//    val comp = codeRess.foldLeft(Occurrences.of(terminal))(_ ++ _.composition)
    // Comme les codeRess sont tous bound, c'est juste l'occurrences.of de l'arg qu'on souhaite, pas sa composition!
//    val comp = codeRess.foldLeft(Occurrences.of(terminal))((acc, arg) => acc ++ Occurrences.of(arg.terminal))
    CodeRes(terminal, ctxs.addBoundDef(terminal))
  }

  final def unplugged(c: Code)(using env: Env, ctxs: Ctxs): Option[(CodeRes, Occurrences)] =
    unplugMap.get((c, env)).flatMap(_.get(ctxs))

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Expr -> Code

  final def codeOfExpr(e: Expr)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    val tpe = e.getType
    val res = e match {
      case v: Variable =>
        val c = subst.get(v).getOrElse(codeOfVarId(idOfVariable(v)))
        return CodeRes(c, ctxs) // C'est un binding, la simplif. a déjà été faite

      case l: Literal[_] => CodeRes(codeOfLit(l), ctxs)

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val ctxsThen = rcond.ctxs.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using env, ctxsThen)
        val ctxsEls = rcond.ctxs.withNegatedCond(rcond.terminal)
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
        val rbody = codeOfExpr(body)(using env.incIf(lab))
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
      case Annotated(e, _) => codeOfExpr(e)
        /*
        // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
        //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
        //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
        codeOfExprsBound(e, tpe)(mkAnnot(_, flags))
        */

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
      case LargeArray(elems, default, size, base) =>
        if (elems.nonEmpty) throw UnsupportedOperationException("elems is not empty")
        codeOfExprsBound(default, size, tpe)(mkLargeArray(Map.empty, _, _, base))
      case ArraySelect(array, index) => codeOfExprsBound(array, index, tpe)(mkArraySelect)
      case ArrayUpdated(array, index, v) => codeOfExprsBound(array, index, v, tpe)(mkArrayUpdated)
      case ArrayLength(array) => codeOfExprsBound(array, tpe)(mkArrayLength)

      case FiniteMap(pairs, default, keyType, valueType) =>
        codeOfExprsBound(pairs.flatMap(p => Seq(p._1, p._2)) :+ default, tpe) {
          case cPairs :+ cDefault =>
            assert(cPairs.size == 2 * pairs.size)
            val cElems = cPairs.grouped(2).map { case Seq(fst, snd) => (fst, snd) }.toSeq
            mkFiniteMap(cElems, cDefault, keyType, valueType)
        }
      case MapApply(map, key) => codeOfExprsBound(map, key, tpe)(mkMapApply)
      case MapUpdated(map, key, value) => codeOfExprsBound(map, key, value, tpe)(mkMapUpdated)

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
        throw new UnsupportedOperationException("computeSignature: Do not know how to handle "+e)
    }
    assert(ctxs.isPrefixOf(res.ctxs))
    simplifyTopLvl(res)
  }

  // Signature de Not(child)
  def negExprOf(child: Expr)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    assert(child.getType == BoolTy)

    child match {
      case Not(e) => codeOfExpr(e)
      case LessThan(lhs, rhs) => codeOfExpr(GreaterEquals(lhs, rhs))
      case GreaterEquals(lhs, rhs) => codeOfExpr(LessThan(lhs, rhs))
      case GreaterThan(lhs, rhs) => codeOfExpr(LessEquals(lhs, rhs))
      case LessEquals(lhs, rhs) => codeOfExpr(GreaterThan(lhs, rhs))
      case And(es) => codeOfExpr(Or(es.map(Not.apply)))
      // Remarque: comme on ne peut pas trier par taille (pour OCBSL), on fait simplement un simplifiedDisjunction
      case _ =>
        val rchild = codeOfExpr(child)
        val negChild = negCodeOf(rchild.terminal)
        rchild.derived(negChild)
    }
  }

  final def codeOfExprsBound(es: Seq[Expr], tpe: Type)(cons: Seq[Code] => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), tpe))

  final def codeOfExprsBound(e1: Expr, tpe: Type)(cons: Code => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1), tpe) { case Seq(c1) => cons(c1) }

  final def codeOfExprsBound(e1: Expr, e2: Expr, tpe: Type)(cons: (Code, Code) => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2), tpe) { case Seq(c1, c2) => cons(c1, c2) }

  final def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, tpe: Type)(cons: (Code, Code, Code) => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), tpe) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  // TODO: Très mal nommé!!! C'est slmt pour les expr du type C(args) sans control flow etc.
  final def codeOfExprsBound(es: Seq[Expr])(cons: Seq[Code] => Code)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    val (newCtxs, codeRess) = es.foldLeft((ctxs, Seq.empty[CodeRes])) {
      case ((ctxs, codeResAcc), e) =>
        val codeResE = codeOfExpr(e)(using env, ctxs)
        assert(ctxs.isPrefixOf(codeResE.ctxs))
        (codeResE.ctxs, codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess)(cons)(using env, newCtxs)
  }

  case class CodeResMatchCase(mc: LabMatchCase, composition: Occurrences)

  final def signatureOfCase(scrut: Code, mc: MatchCase)(using env: Env, ctxs0: Ctxs, subst0: LetValSubst): (CodeResMatchCase, Seq[Code]) = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")
    given ô_ô: LetValSubst = sys.error("Carefully select subst")

    def convertPattern(scrut: Code, pat: Pattern, subst0: LetValSubst): (LabelledPattern, LetValSubst) = {
      val subst1 = pat.binder.map(vd => subst0 + (vd.toVariable -> scrut)).getOrElse(subst0)

      def recHelper(subScruts: Seq[Code], subps: Seq[Pattern]): (Seq[LabelledPattern], LetValSubst) = {
        assert(subScruts.size == subps.size)
        subScruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], subst1)) {
          case ((acc, subst), (subScrut, subp)) =>
            val (rsub, subst2) = convertPattern(subScrut, subp, subst)
            (acc :+ rsub, subst2)
        }
      }

      pat match {
        case WildcardPattern(_) => (LabelledPattern.Wildcard, subst1)
        case LiteralPattern(_, lit) => (LabelledPattern.Lit(lit), subst1)
        case ADTPattern(_, id, tps, subps) =>
          val subScruts = adtSubScrutinees(scrut, ADTType(id, tps))
          val (rsubs, subst2) = recHelper(subScruts, subps)
          (LabelledPattern.ADT(id, tps, rsubs), subst2)
        case TuplePattern(_, subps) =>
          val tt@TupleType(_) = codeTpe(scrut)
          val subScruts = tupleSubscrutinees(scrut, tt)
          val (rsubs, subst2) = recHelper(subScruts, subps)
          (LabelledPattern.TuplePattern(rsubs), subst2)
        case UnapplyPattern(_, recs, id, tps, subps) =>
          if (recs.nonEmpty) throw UnsupportedOperationException("recs is not empty")
          val unapp = unapplySubScrutinees(scrut, id, tps)
          val (rsubs, subst2) = recHelper(unapp.subs, subps)
          (LabelledPattern.Unapply(Seq.empty, id, tps, rsubs), subst2)
      }
    }

    val (labPat, subst1) = convertPattern(scrut, mc.pattern, subst0)
    val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, labPat)

    // TODO: On pourrait conserver le ctx des guard pour le body? En gros, qu'on plug le body dans le ctx de guard
    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using env, ctxs1, subst1))
    val (compGuard, cGuard) = rguard.map(_.selfPlugged(ctxs1)).getOrElse((Occurrences.empty, trueCode))

    val rhsCtxs = ctxs1.withCond(cGuard)
    val rrhs = codeOfExpr(mc.rhs)(using env, rhsCtxs, subst1)
    val (compRhs, rhs) = rrhs.selfPlugged(rhsCtxs)

    val labMc = LabMatchCase(labPat, cGuard, rhs)
    (CodeResMatchCase(labMc, compGuard ++ compRhs), patConds :+ cGuard)
  }

  final def signatureOfCases(cScrut: Code, mcs: Seq[MatchCase], acc: Seq[CodeResMatchCase])
                            (using env: Env, ctxs: Ctxs, subst: LetValSubst): Seq[CodeResMatchCase] = {
    if (mcs.isEmpty) acc
    else {
      val (newMatchCase, caseConds) = signatureOfCase(cScrut, mcs.head)
      val negCaseConds = negatedConjunction(caseConds)
      signatureOfCases(cScrut, mcs.tail, acc :+ newMatchCase)(using env, ctxs.withCond(negCaseConds))
    }
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Common to OCBSL and OL

  def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean

  def doSimplifyDisjunction(disj0: Seq[Code])(using Env, Ctxs): Seq[Code]

  def checkForContradiction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Option[Int]

  final def simplifiedDisjunction(disj0: Seq[Code], polarity: Boolean)(using Env, Ctxs): Code = {
    assert(disj0.forall(c => codeTpe(c) == BoolTy))
    val disjs1 = unOrCodes(disj0).filter(_ != falseCode).distinct
    val disjs2 = doSimplifyDisjunction(disjs1)
    val simp = {
      if (disjs2.isEmpty) falseCode
      else if (disjs2.size == 1) disjs2.head
      else {
        val lastKeptIx = Some(disjs2.indexOf(trueCode)).filter(_ >= 0)
          .orElse(checkForContradiction(disjs2, polarity))
          .getOrElse(disjs2.length - 1)

        if (lastKeptIx == disjs2.length - 1 && disjs2.last != trueCode) {
          // Nothing simplified, so just make the disjunction and return
          // TODO: Sort if "truly pure" and not pure due to binding!
          // val disjs2 = if (purities.forall(_.isPure)) disjs1.sorted else disjs1
          codeOfSig(mkOr(disjs2), BoolTy)
        } else {
          // Due to short-circuiting, once the disjunction evaluates to true, the remaining disjuncts won't ever be evaluated
          // so it is safe to drop them -- including impure expressions.
          val disjs3 = disjs2.take(lastKeptIx + 1)
          val disjs3Purities = disjs3.map(codePurity)
          // TODO: Pureté imprécise! Il faudrait accumuler les disjs
          if (disjs3Purities.forall(_.isPure)) trueCode
          else {
            // Add a trailing `true` if not already present (because the disjunction will evaluate to true,
            // but due to the presence of impure expressions, we are not allowed to simplify the whole expr to true
            val disjs4 = if (disjs3.contains(trueCode)) disjs3 else disjs3 :+ trueCode
            codeOfSig(mkOr(disjs4), BoolTy)
          }
        }
      }
    }
    if (polarity) simp else negCodeOf(simp)
  }

  final def tryFoldLeftDisjunction[E, T](disjs: Seq[Code], init: T)
                                        (f: Ctxs ?=> (T, Code) => Either[E, T])
                                        (using env: Env, ctxs: Ctxs): Either[E, T] = {
    ocbsl.tryFoldLeft(disjs, (init, ctxs)) {
      case ((acc, ctxs), disj) =>
        given Ctxs = ctxs
        f(acc, disj).map { newAcc =>
          val tearedDisj = tearDown(disj)
          assert(tearedDisj.ctxs.isLitVarOrBoundDef(tearedDisj.terminal))
          val newCtxs = tearedDisj.ctxs.withNegatedCond(tearedDisj.terminal)
          (newAcc, newCtxs)
        }
    }.map(_._1)
  }

  final def foldLeftDisjunction[T](disjs: Seq[Code], init: T)(f: Ctxs ?=> (T, Code) => T)(using env: Env, ctxs: Ctxs): T =
    tryFoldLeftDisjunction[Nothing, T](disjs, init)((t, c) => Right(f(t, c))).merge

  final def transformDisjunction[T](disjs: Seq[T])(f: Ctxs ?=> T => CodeRes)(using env: Env, outerCtxs: Ctxs): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    assert(disjs.size >= 2)

    def transformRec(disjs: Seq[T], rdisjsAcc: Seq[CodeRes])(using ctxs: Ctxs): (Seq[CodeRes], Ctxs) = {
      assert(rdisjsAcc.isEmpty || rdisjsAcc.last.ctxs.isPrefixOf(ctxs))
      assert(outerCtxs.isPrefixOf(ctxs))
      if (disjs.isEmpty) (rdisjsAcc, ctxs)
      else {
        val re: CodeRes = f(disjs.head)
        assert(codeTpe(re.terminal) == BoolTy, s"Got ${codeTpe(re.terminal)}")
        assert(ctxs.isPrefixOf(re.ctxs))
        val neg = negCodeOf(re.terminal)
        val newCtxs = re.ctxs.withCond(neg)
        if (neg == falseCode) (rdisjsAcc :+ re, newCtxs) // On s'arrête ici, et on ajoute en effet false dans les conds, c'est voulu. Cela permet d'avoir le comportement inverse avec combineRec
        else transformRec(disjs.tail, rdisjsAcc :+ re)(using newCtxs)
      }
    }

    def combineRec(disjs: Seq[CodeRes], acc: CodeRes): CodeRes = {
      disjs match {
        case Seq() => acc
        case init :+ last =>
          assert(last.ctxs.isPrefixOf(acc.ctxs))
          assert(init.forall(_.ctxs.isPrefixOf(last.ctxs)))
          assert(init.forall(i => outerCtxs.isPrefixOf(i.ctxs)))

          if (last.terminal == falseCode) {
            // On skip celui-ci (on ne drop pas son ctxs, car il est préfixe de acc par construction de transformRec)
            combineRec(init, acc)
          } else {
            val (pluggedOcc, accPlugged) = acc.selfPlugged(last.ctxs.withNegatedCond(last.terminal))
            val newAcc = simplifiedDisjunctionCodeRes(last, accPlugged, polarity = true)
            val res = combineRec(init, newAcc)
            val noTailRecPls = Ctxs(last.ctxs.ctxs)
            res
          }
      }
    }

    val (disjsCodeRes, lastCtxs) = transformRec(disjs, Seq.empty)(using outerCtxs)
    assert(disjsCodeRes.last.ctxs.isPrefixOf(lastCtxs))
    val res = combineRec(disjsCodeRes, CodeRes(falseCode, lastCtxs))
    res
  }

  // TODO: Explication
  def simplifiedDisjunctionCodeRes(lhs: CodeRes, rhs: Code, polarity: Boolean)(using env: Env): CodeRes = {
    // TODO: Pas si vite! newDisjs peut très bien retourner un non terminal!
    val simpDisjs = simplifiedDisjunction(Seq(lhs.terminal, rhs), polarity)(using env, lhs.ctxs)
    val newCtxs = lhs.ctxs.pop match {
      case Some((prevCtxs, Ctx.BoundDef(bnd))) if bnd == lhs.terminal && code2sig(lhs.terminal).label == Label.Or => // TODO: Quid si Not?
        prevCtxs.addBoundDef(simpDisjs)
      case _ => lhs.ctxs.addBoundDef(simpDisjs)
    }
    CodeRes(simpDisjs, newCtxs)
  }

  final def negCodeResOf(c: Code)(using env: Env, ctxs: Ctxs): CodeRes = negCodeResOf(c)(_ => true)

  final def negCodeResOf(c: Code)(mayRmNeg: Ctxs ?=> Code => Boolean)(using env: Env, ctxs: Ctxs): CodeRes = {
    assert(codeTpe(c) == BoolTy, s"Got ${codeTpe(c)}")
    if (CodeRes.isTerminal(c)) {
      // assert(ctxs.isLitVarOrBoundDef(c)) // TODO: CovList n°16 fails ?
      val neg = code2sig(c) match {
        case Signature(Label.Not | Label.LessEquals |
                       Label.LessThan | Label.GreaterEquals | Label.GreaterThan |
                       Label.Lit(_), _) if mayRmNeg(c) =>
          negCodeOf(c)
        case _ =>
          // TODO: Push la négation pour IfExpr et MatchExpr?
          codeOfSig(mkNot(c), BoolTy)
      }
      CodeRes(neg, ctxs.addBoundDef(neg))
    } else {
      val teared = tearDown(c)
      negCodeResOf(teared.terminal)(mayRmNeg)(using env, teared.ctxs)
    }
  }

  final def negCodeOf(c: Code): Code = {
    assert(codeTpe(c) == BoolTy, s"Got ${codeTpe(c)}")
    code2sig(c) match {
      case Signature(Label.Not, Seq(cc)) => cc
      case BoolLitSig(b) => b2c(!b)
      case LtSig(lhs, rhs) => codeOfSig(mkGreaterEquals(lhs, rhs), BoolTy)
      case GeqSig(lhs, rhs) => codeOfSig(mkLessThan(lhs, rhs), BoolTy)
      case GtSig(lhs, rhs) => codeOfSig(mkLessEquals(lhs, rhs), BoolTy)
      case LeqSig(lhs, rhs) => codeOfSig(mkGreaterThan(lhs, rhs), BoolTy)
      case _ =>
        // TODO: Push la négation pour IfExpr et MatchExpr?
        codeOfSig(mkNot(c), BoolTy)
    }
  }

  final def conjunct(conj: Seq[Code])(using Env, Ctxs): Code = simplifiedDisjunction(conj.map(negCodeOf), polarity = false)

  final def negatedConjunction(conj: Seq[Code])(using Env, Ctxs): Code = simplifiedDisjunction(conj.map(negCodeOf), polarity = true)

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Code general simplification

  // TODO: Si cr.terminal != cr.ctxs.last, alors c'est une occurrences lié qu'il ne faudrait pas simplifier, n'est-ce pas???
  //  --> Oui et non, car dans certains cas, on peut avoir des simplifications extra grace a un ctx enrichi
  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  // TODO: Peut importe la pureté pour les simplifs, parce que les ctx vont garantir un bind si nécessaire, n'est-ce pas?
  final def simplifyTopLvl(cr: CodeRes)(using env: Env): CodeRes = {
    val tpe = codeTpe(cr.terminal)
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)

    val simp = code2sig(cr.terminal) match {
      case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
        assert(CodeRes.isTerminal(cond))
        assert(cr.ctxs.isLitVarOrBoundDef(cond))

        // 1. Si cr.ctxs contient ce code en dernier BoundDef, cela signifie qu'on va simplifier la "définition"
        // (dans l'équivalent let v = e, on est sur le point de simplifier 'e')
        // 2. Sinon, alors cr.terminal est une occurrence liée par un BoundDef ultérieur
        // (dans l'équivalent let v = e in body, on se trouve qqpart dans body, et on va simplifier 'v')
        // Dans le cas 1, on utilise le contexte mais sans ce BoundDef
        // Dans le cas 2, on utilise simplement cr.ctxs
        val (prevCtxs, condCtxs) = cr.ctxs.ctxs match {
          case prevCtxs :+ (bCond@Ctx.BoundDef(cond2)) :+ Ctx.BoundDef(ifExpr2) if cond2 == cond && cr.terminal == ifExpr2 =>
            (Ctxs(prevCtxs), Ctxs(prevCtxs :+ bCond))

          case prevCtxs :+ Ctx.BoundDef(ifExpr2) if cr.terminal == ifExpr2 =>
            val prevCtxss = Ctxs(prevCtxs)
            assert(prevCtxss.isLitVarOrBoundDef(cond))
            (prevCtxss, prevCtxss)

          case _ =>
            assert(cr.ctxs.isLitVarOrBoundDef(cond))
            (cr.ctxs, cr.ctxs)
        }
        val condCr = CodeRes(cond, condCtxs)
        val ctxsForThen = condCtxs.withCond(cond)
        val ctxsForEls = condCtxs.withNegatedCond(cond)

        val fstTry: Option[CodeRes] = {
          // Remarque: pas besoin de la pureté:
          //  -Pour cond: car bound
          //  -Pour la branche "morte": car unreachable
          if (cond == trueCode || thenn == els) {
            val Some((thennCr, _)) = unplugged(thenn)(using env, ctxsForThen)
            assert(ctxsForThen.isPrefixOf(thennCr.ctxs))
            Some(thennCr)
          } else if (cond == falseCode) {
            val Some((elsCr, _)) = unplugged(els)(using env, ctxsForEls)
            assert(ctxsForEls.isPrefixOf(elsCr.ctxs))
            Some(elsCr)
          } else None
        }
        def sndTry: CodeRes = (code2sig(thenn), code2sig(els)) match {
          case (BoolLitSig(true), BoolLitSig(false)) => CodeRes(cond, condCtxs)

          case (BoolLitSig(false), BoolLitSig(true)) =>
            val negCond = negCodeOf(cond)
            CodeRes(negCond, condCtxs.addBoundDef(negCond))

          case (BoolLitSig(true), _) =>
            simplifiedDisjunctionCodeRes(condCr, els, polarity = true)

          case (_, BoolLitSig(true)) =>
            val negCond = negCodeResOf(cond)(using env, condCtxs)
            simplifiedDisjunctionCodeRes(negCond, thenn, polarity = true)

          // TODO: Là où il y a des negCodeOf, on pourrait plutôt utiliser negCodeResOf pr hoist du ctx...
          case (BoolLitSig(false), _) =>
            // -> !cond && els === !(cond || !els)
            simplifiedDisjunctionCodeRes(condCr, negCodeOf(els), polarity = false)

          case (_, BoolLitSig(false)) =>
            // -> cond && then === !(!cond || !thenn)
            val negCond = negCodeResOf(cond)(using env, condCtxs)
            simplifiedDisjunctionCodeRes(negCond, negCodeOf(thenn), polarity = false)

          case (Signature(Label.IfExpr, Seq(cond2, thenn2, `els`)), _) =>
            // -> if (cond && cond2) thenn2 else els === if (!(!cond || !cond2)) thenn2 else els
            val negCond = negCodeResOf(cond)(using env, condCtxs)
            val negCond2 = negCodeOf(cond2)
            val combinedCond = simplifiedDisjunctionCodeRes(negCond, negCond2, polarity = false)
            val newIfCode = codeOfSig(mkIfExpr(combinedCond.terminal, thenn2, els), tpe)
            combinedCond.derived(newIfCode)

          case (_, Signature(Label.IfExpr, Seq(cond2, `thenn`, els2))) =>
            // -> if (cond || cond2) thenn else els2
            val combinedCond = simplifiedDisjunctionCodeRes(condCr, cond2, polarity = true)
            val newIfCode = codeOfSig(mkIfExpr(combinedCond.terminal, thenn, els2), tpe)
            combinedCond.derived(newIfCode)

          case _ => cr
        }
        fstTry.getOrElse(sndTry)

      case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
        // TODO: Ne devrait-on pas évaluer cette condition ds le ctx précédent? Mais comme c'est un bind, cela ne devrait rien changer
        isConstructor(e, adt, id)(using env, cr.ctxs) match {
          case Some(b) => cr.derived(b2c(b))
          case None => cr
        }

      case Signature(lab@Label.ADTSelector(_, _, _), Seq(e)) =>
        cr.derived(adtSelect(e, lab, tpe))

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
                  isConstructor(base, ADTType(id, tps), id)(using env, cr.ctxs) == Some(true) =>
                sameBase(i + 1, Some(base))
              case _ => None // L'aventure se termine ici
            }
          }
        }

        sameBase(0, None) match {
          case Some(base) => cr.derived(base)
          case None => cr
        }

      case Signature(Label.TupleSelect(i), Seq(e)) =>
        cr.derived(tupleSelect(e, i, tpe))

      case Signature(Label.ArraySelect, Seq(arr, i)) =>
        def collectIndicesValues(arr: Code, indices: Map[Code, Code]): Map[Code, Code] = code2sig(arr) match {
          case Signature(Label.ArrayUpdated, Seq(arr2, j, newValue)) =>
            collectIndicesValues(arr2, addIfAbsent(indices)(j -> newValue))
          case Signature(Label.LargeArray(_, _), _ :+ default :+ _) =>
            addIfAbsent(indices)(i -> default)
          case Signature(Label.FiniteArray(_), elems) =>
            code2sig(i) match {
              case Signature(Label.Lit(Int32Literal(ii)), _) => addIfAbsent(indices)(i -> elems(ii))
              case _ => indices
            }
          case _ => indices
        }
        collectIndicesValues(arr, Map.empty)
          .get(i).map(cr.derived)
          .getOrElse(cr)

      case Signature(Label.ArrayLength, Seq(arr)) =>
        def getLen(currArr: Code): CodeRes = code2sig(currArr) match {
          case Signature(Label.ArrayUpdated, Seq(newArr, _, _)) => getLen(newArr)
          case Signature(Label.FiniteArray(_), elems) =>
            cr.derived(codeOfLit(Int32Literal(elems.size)))
          case Signature(Label.LargeArray(_, _), _ :+ _ :+ size) =>
            cr.derived(size)
          case _ =>
            if (currArr == arr) cr
            else cr.derived(codeOfSig(mkArrayLength(currArr), tpe))
        }
        getLen(arr)

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
        else (code2sig(e1), code2sig(e2)) match {
          case (IntLikeLitSig(b1), IntLikeLitSig(b2)) =>
            val res = lab match {
              case Label.Equals => b1 == b2 // should already be taken care of by e1 == e2 above
              case Label.GreaterEquals => b1 >= b2
              case Label.LessEquals => b1 <= b2
              case Label.LessThan => b1 < b2
              case Label.GreaterThan => b1 > b2
            }
            cr.derived(b2c(res))
          case _ => cr
        }

      case Signature(Label.UMinus, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.UMinus, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(lab@(Label.Plus | Label.Times), Seq(e1, e2)) =>
        cr.derived(simplifyAssocArith(lab, e1, e2))

      case Signature(Label.Minus, Seq(e1, e2)) =>
        assert(codeTpe(e1) == codeTpe(e2))
        if (e1 == e2) cr.derived(zero)
        else (code2sig(e1), code2sig(e2)) match {
          case (IntLikeLitSig(i1), IntLikeLitSig(i2)) =>
            cr.derived(codeOfIntLit(i1 - i2, codeTpe(e1)))
          case _ => cr
        }

      case Signature(lab@(Label.Division | Label.Remainder | Label.Modulo), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Division => one
          case Label.Remainder | Label.Modulo => zero
        }
        if (opts.assumeChecked && e2 != zero && e1 == zero) cr.derived(zero)
        else if (opts.assumeChecked && e2 != zero && e1 == e2) cr.derived(resIfEq)
        else (code2sig(e1), code2sig(e2)) match {
          case (IntLikeLitSig(i1), IntLikeLitSig(i2)) if i2 != 0 =>
            val res = lab match {
              case Label.Division => i1 / i2
              case Label.Remainder => i1 % i2
              case Label.Modulo => if (i2 < 0) i1 mod (-i2) else i1 mod i2
            }
            cr.derived(codeOfIntLit(res, codeTpe(e1)))
          case _ => cr
        }

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
        assert(CodeRes.isTerminal(scrut))
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val cases = pats.zip(guards).zip(rhss).map {
          case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
        }
        // Voir explication IfExpr
        val scrutCr = cr.ctxs.ctxs match {
          case prevCtxs :+ (bScrut@Ctx.BoundDef(scrut2)) :+ Ctx.BoundDef(match2) if scrut2 == scrut && cr.terminal == match2 =>
            CodeRes(scrut, Ctxs(prevCtxs :+ bScrut))

          case prevCtxs :+ Ctx.BoundDef(match2) if cr.terminal == match2 =>
            val prevCtxss = Ctxs(prevCtxs)
            assert(prevCtxss.isLitVarOrBoundDef(scrut))
            CodeRes(scrut, prevCtxss)

          case _ =>
            assert(cr.ctxs.isLitVarOrBoundDef(scrut))
            CodeRes(scrut, cr.ctxs)
        }
        simplifyCases(scrut, cases)(using env, scrutCr.ctxs) match {
          case SimplifiedCases.Empty => sys.error("ah bah là, je sais pas quoi faire...")
          case SimplifiedCases.ElidableMatchExpr(rhs) => rhs
          case SimplifiedCases.Cases(newCases) =>
            CodeRes.matchExpr(scrutCr, newCases, tpe)
        }

      // TODO: For Or: call to simplify?

      case _ => cr
    }

    if (tpe == BoolTy) {
      given Ctxs = cr.ctxs
      if (implied(cr.terminal)) simp.derived(trueCode)
      else if (implied(negCodeOf(simp.terminal))) simp.derived(falseCode)
      else simp
    }
    else simp
  }

  final def adtSelect(recv: Code, lab: Label.ADTSelector, tpe: Type): Code = {
    code2sig(recv) match {
      case Signature(Label.ADT(id, _), args) if id == lab.ctor.id =>
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
        val index = lab.ctor.definition.selectorID2Index(lab.selector)
        args(index)
      case _ => codeOfSig(mkADTSelector(recv, lab.adt, lab.ctor, lab.selector), tpe)
    }
  }

  final def tupleSelect(recv: Code, i: Int, tpe: Type): Code = {
    assert(i >= 1)
    code2sig(recv) match {
      case Signature(Label.Tuple, args) => args(i - 1)
      case _ => codeOfSig(mkTupleSelect(recv, i), tpe)
    }
  }

  final def simplifyAssocArith(op: Label.Plus.type | Label.Times.type, lhs: Code, rhs: Code): Code = {
    assert(codeTpe(lhs) == codeTpe(rhs))
    val tpe = codeTpe(lhs)
    val neutral = if (op == Label.Plus) 0 else 1

    def flatten(c: Code): Seq[Code] = code2sig(c) match {
      case Signature(`op`, Seq(c1, c2)) => flatten(c1) ++ flatten(c2)
      case _ => Seq(c)
    }
    def cstFold(remaining: Seq[Code], acc: Seq[Code], cst: BigInt): (Seq[Code], BigInt) = remaining match {
      case Seq() => (acc, cst)
      case h +: rest => code2sig(h) match {
        case IntLikeLitSig(c) =>
          if (op == Label.Plus) cstFold(rest, acc, cst + c)
          else {
            if (c == 0) (Seq.empty, 0)
            else cstFold(rest, acc, cst * c)
          }
        case _ => cstFold(rest, acc :+ h, cst)
      }
    }
    def recons(terms0: Seq[Code]): Code = {
      assert(terms0.nonEmpty)
      if (terms0.size == 1) terms0.head
      else {
        val terms = terms0.sorted
        val sig = if (op == Label.Plus) mkPlus(terms) else mkTimes(terms)
        codeOfSig(sig, tpe)
      }
    }

    val terms = flatten(lhs) ++ flatten(rhs)
    val (nonLits, cst) = cstFold(terms, Seq.empty, neutral)
    lazy val cstCode = codeOfIntLit(cst, tpe)
    if (nonLits.isEmpty) cstCode
    else if (cst == neutral) recons(nonLits)
    else recons(nonLits :+ cstCode)
  }

  enum SimplifiedCase {
    case Unreachable
    case Covered(rhsCtxs: Ctxs, comp: Occurrences)
    case Unchanged(rhsCtxs: Ctxs, caseConds: Seq[Code], comp: Occurrences)
  }

  enum SimplifiedCases {
    case Empty
    case ElidableMatchExpr(rhs: CodeRes)
    case Cases(res: Seq[CodeResMatchCase])
  }

  final def simplifyCase(scrut: Code, matchCase: LabMatchCase)(using env: Env, ctxs0: Ctxs): SimplifiedCase = {
    assert(ctxs0.isLitVarOrBoundDef(scrut))
    val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, matchCase.pattern)
    given Ctxs = ctxs1
    val rhsCtxs = ctxs1.withCond(matchCase.guard)
    val caseConds = patConds :+ matchCase.guard

    lazy val guardComp = occurrencesOf(matchCase.guard)(using env, ctxs1)
    lazy val bodyComp = occurrencesOf(matchCase.rhs)(using env, rhsCtxs)
    lazy val unchanged = SimplifiedCase.Unchanged(rhsCtxs, caseConds, guardComp ++ bodyComp)

    // TODO: Ok? Après tout, ctxs1 contient les binding et les conds!!!
    // TODO: ou alors: pure sauf s'il y a des unapply, dans ce cas on check fnpurity des unapply
    if (caseConds.forall(c => codePurity(c).isPure)) {
      given Ctxs = ctxs1
      val caseCondsConj = conjunct(caseConds)
      lazy val negCondsConj = negatedConjunction(caseConds)
      if (implied(caseCondsConj)) SimplifiedCase.Covered(rhsCtxs, guardComp ++ bodyComp)
      else if (implied(negCondsConj)) SimplifiedCase.Unreachable
      else unchanged
    } else unchanged
  }

  final def simplifyCases(scrut: Code, cases: Seq[LabMatchCase])(using env: Env, ctxs: Ctxs): SimplifiedCases = {
    assert(ctxs.isLitVarOrBoundDef(scrut))

    def mkElidable(caseRhs: Code, rhsCtxs: Ctxs): SimplifiedCases.ElidableMatchExpr = {
      assert(ctxs.isPrefixOf(rhsCtxs))
      val Some((rhsUnpl, _)) = unplugged(caseRhs)(using env, rhsCtxs)
      assert(rhsCtxs.isPrefixOf(rhsUnpl.ctxs))
      SimplifiedCases.ElidableMatchExpr(rhsUnpl)
    }

    def acc2cases(acc: Seq[(LabMatchCase, Ctxs, Occurrences)]): Seq[CodeResMatchCase] =
      acc.map { case (lmc, _, occ) => CodeResMatchCase(lmc, occ) }

    def rec(cases: Seq[LabMatchCase], acc: Seq[(LabMatchCase, Ctxs, Occurrences)])(using ctxs: Ctxs): SimplifiedCases = cases match {
      case Seq() =>
        acc match {
          case Seq() => SimplifiedCases.Empty
          case Seq((soleCase, rhsCtxs, _)) => mkElidable(soleCase.rhs, rhsCtxs)
          case (fst, fstCtxs, _) +: rest =>
            // TODO: Ok? Quid pureté des caseConds?
            val allSameBodies = rest.forall(_._1.rhs == fst.rhs)
            if (allSameBodies) mkElidable(fst.rhs, fstCtxs)
            else SimplifiedCases.Cases(acc2cases(acc))
        }
      case currCase +: rest =>
        simplifyCase(scrut, currCase) match {
          case SimplifiedCase.Unreachable => rec(rest, acc)
          case SimplifiedCase.Covered(rhsCtxs, comp) =>
            if (acc.isEmpty) {
              mkElidable(currCase.rhs, rhsCtxs)
            } else {
              val wildcard = LabMatchCase(LabelledPattern.Wildcard, currCase.guard, currCase.rhs)
              SimplifiedCases.Cases(acc2cases(acc) :+ CodeResMatchCase(wildcard, comp))
            }
          case SimplifiedCase.Unchanged(rhsCtxs, caseConds, comp) =>
            val negCaseConds = negatedConjunction(caseConds)
            val res = rec(rest, acc :+ (currCase, rhsCtxs, comp))(using ctxs.withCond(negCaseConds))
            val noTailRecPls = Ctxs(ctxs.ctxs)
            res
        }
    }

    rec(cases, Seq.empty)
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Purity

  final def codePurity(c: Code)(using env: Env, ctxs: Ctxs): Purity =
    codePurityInst.codePurity(c)(using env.copy(forceBinding = true))

  final class CodePurity extends CodeTryFolder[Unit, Purity] {
    override type Extra = Unit

    private val visitingFns = mutable.Set.empty[Identifier]
    private val purityCache = mutable.Map.empty[Identifier, Boolean]
    private val codePurityCache = mutable.Map.empty[Code, Boolean]
    private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
    private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
    private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V

    def codePurity(c: Code)(using Env, Ctxs): Purity = tryFold(c, Pure, ()).getOrElse(Impure)

    // TODO: Ok? Après tout, ctxs1 contient les binding et les conds!!!
    // TODO: ou alors: pure sauf s'il y a des unapply, dans ce cas on check fnpurity des unapply
    def tryFoldPatternConditions(patConds: Seq[Code], acc: Purity, extra: Unit)(using Env, Ctxs): Either[Unit, Purity] =
      acc ++ foldPurity(patConds) match {
        case Impure => Left(())
        case p => Right(p)
      }

    def foldPurity(cs: Seq[Code])(using env: Env, ctxs: Ctxs): Purity = {
      assert(cs.forall(CodeRes.isTerminal))
      cs.foldLeft((ctxs, Pure)) {
        case ((ctxs, acc), c) =>
          given Ctxs = ctxs
          lazy val purity = codePurity(c)
          (ctxs.addBoundDef(c), acc ++ purity)
      }._2
    }

    override def tryFoldImpl(c: Code, acc: Purity, extra: Unit)(using env: Env, ctxs: Ctxs): Either[Unit, Purity] = {
      if (acc == Impure) Left(())
      else if (ctxs.isBoundDef(c)) Right(acc)
      else {
        val purityC = code2sig(c) match {
          case Signature(Label.Var(_) | Label.Lit(_), Seq()) => Pure
          case Signature(Label.Assume, Seq(pred, body)) =>
            assert(CodeRes.isTerminal(pred))
            if (pred == trueCode) codePurity(body) // pas besoin de ctxs.withCond car de toute façon c'est true
            else Impure

          case Signature(Label.Assert | Label.Require, Seq(pred, body)) =>
            assert(CodeRes.isTerminal(pred))
            val pBody = codePurity(body)(using env, ctxs.withCond(pred))
            if (pred == trueCode) pBody
            else assmChkPurity ++ pBody // Pureté comme Stainless

          // TODO: If cond true/false, only consider one of the branch

          case Signature(Label.Ensuring, Seq(body, pred)) =>
            code2sig(pred) match {
              case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => codePurity(body)
              case _ => Impure
            }

          case Signature(Label.ADTSelector(adt, ctor, _), Seq(e)) =>
            assert(CodeRes.isTerminal(e))
            if (opts.assumeChecked || isConstructor(e, adt, ctor.id) == Some(true)) codePurity(e)
            else Impure

          case Signature(Label.ADT(id, tps), args) =>
            assert(args.forall(CodeRes.isTerminal))
            // TODO: Ok? Il y a un commentaire dans SWP...
            val ctor: TypedADTConstructor = getConstructor(id, tps)
            val consingPurity = {
              if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
              else Impure
            }
            consingPurity ++ foldPurity(args)

          case Signature(Label.Lambda(_), Seq(_)) => Pure

          case Signature(Label.FunctionInvocation(id, _), args) =>
            foldPurity(args) ++ fnPurity(id)

          case Signature(Label.Application, callee +: args) =>
            assert(CodeRes.isTerminal(callee))
            assert(args.forall(CodeRes.isTerminal))
            // TODO: L'orig ignore callee, mais si on fait ça, on risque de faire du reordering dans certains cas (comme ContMonad)
            // TODO: Dans SWP: quid pureté callee???
            // TODO: Pureté ok? Après tout, un inline de lambda peut donner lieu à impure...
            lazy val calleePurity = code2sig(callee) match {
              case Signature(Label.Lambda(params), Seq(body)) =>
                assert(params.size == args.size)
                // Le ctxs où la lambda a été définie: on regarde dans le body,
                // car si on codePurity sur la lambda elle-même, on aura de toute façon Pure
                val lambdaCtxs = ctxs.takeUntilDefined(callee)
                codePurity(body)(using env.inc, lambdaCtxs)
              case Signature(Label.Var(_), Seq()) => Pure // TODO: Comme c'est une free var et qu'on en sait rien à son sujet...
              case _ => Impure
            }
            assmChkPurity ++ calleePurity ++ foldPurity(args)(using env, ctxs.addBoundDef(callee))

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
        if (purity == Impure) Left(()) else Right(purity)
      }
    }

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
            codePurityCache += blockedCode -> isPure
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

      if (visitingFns.contains(fn)) {
        if (!opts.assumeChecked) Impure
        else Delayed(Set(fn))
      } else {
        purityCache.get(fn) match {
          case Some(true) => Pure
          case Some(false) => Impure
          case None if fnBlockedBy.contains(fn) => Delayed(fnBlockedBy(fn))
          case None =>
            given Env = Env(LambdaNesting(0), forceBinding = true)
            given Ctxs = Ctxs.empty
            given LetValSubst = LetValSubst.empty

            assert(!visitingFns.contains(fn))
            assert(!fnBlockedBy.contains(fn))
            assert(!blocking.contains(fn))
            visitingFns += fn
            val bodyCodeRes = codeOfExpr(getFunction(fn).fullBody)
            val bodyCode = bodyCodeRes.selfPlugged(Ctxs.empty)._2
            // val uncodedTest = uncodeOf(bodyCode)(using RevEnv(Map.empty, LambdaNesting(0)))
            val purity = codePurity(bodyCode)
            visitingFns -= fn
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
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Composition of codes, binding, inlining

  enum BindingCase {
    // In let v = e in body...
    case Elidable // ... the `e` (and the let) can be removed (that is, we can just return `body`, `e` is pure)
    case Inlinable // ... the `e` can be inlined or bound, but it definitely appears in `body` (may or may not be impure)
    case MustBind // ... the `e` must be bound (appears in `body` if pure, may not appear if impure)
  }

  // x, x.a, x.a.b etc.
  final def isVarOrSelector(c: Code): Boolean = code2sig(c) match {
    case Signature(Label.Var(_), Seq()) => true
    case Signature(Label.ADTSelector(_, _, _), Seq(e)) => isVarOrSelector(e)
    case _ => false
  }

  final def needsBinding(terminal: Code, terminalComposition: Occurrences, bodyOccurrences: Occurrences, inlinedLets: Set[Code])(using env: Env, prefix: Ctxs): BindingCase = {
    assert(!isLitOrVar(terminal))
    assert(!prefix.isBoundDef(terminal))

    code2sig(terminal) match {
      case Signature(Label.Ensuring, _) => BindingCase.Inlinable
      case _ =>
        if (env.forceBinding) BindingCase.MustBind
        else {
          val definitionOccurrence = bodyOccurrences(terminal)
          val terminalIsPure = codePurity(terminal)
          definitionOccurrence match {
            case Occurrence.Many =>
              codeTpe(terminal) match {
                case FunctionType(_, _) if !isLambda(terminal) && isVarOrSelector(terminal) => BindingCase.Inlinable
                case _ =>
                  BindingCase.MustBind
              }
            case Occurrence.Zero =>
              // Si une expr impure n'apparait pas dans le body, on ne peut pas l'éliminer, il faut donc le bind
              if (!terminalIsPure.isPure)
                BindingCase.MustBind
              else BindingCase.Elidable
            case Occurrence.Once(inCtxs, occurrenceNesting, _) if terminalIsPure.isPure =>
              assert(env.nesting.level <= occurrenceNesting.level)
              assert(prefix.impureParts.isPrefixOf(inCtxs))
              if (occurrenceNesting.level != env.nesting.level && terminalComposition.hasLambda) BindingCase.MustBind
              else BindingCase.Inlinable
            case Occurrence.Once(inCtxs, occurrenceNesting, _) =>
              assert(env.nesting.level <= occurrenceNesting.level)
              // TODO: Expliquer cette daube
              // inEnv représente l'env. actif lors de l'occurrence de `terminal` dans le trou que l'on s'apprête à compléter.
              // S'il est différent de l'env ou `terminal` est introduit, alors on a besoin de let-bind, car inline
              // une expr impure après un PC est incorrect.
              assert(prefix.impureParts.isPrefixOf(inCtxs))
              // Dans inCtxs, on nécessairement le binding v -> terminal juste après prefix
              assert(prefix.impureParts.ctxs.size + 1 <= inCtxs.ctxs.size)
              assert(inCtxs.ctxs(prefix.impureParts.ctxs.size) == Ctx.BoundDef(terminal))

              lazy val sequencingPreserved: Boolean = {
                val extras = inCtxs.ctxs.drop(prefix.ctxs.size + 1) // +1 car c'est après ce binding
                extras.forall {
                  case Ctx.Assumed(_) | Ctx.AssumeLike(_, _) => false // Condition supplémentaire; donc impure
                  case Ctx.BoundDef(extra) => inlinedLets(extra)
                }
              }

              if (env.nesting == occurrenceNesting && sequencingPreserved) BindingCase.Inlinable
              else {
                BindingCase.MustBind
              }
          }
        }
    }
  }

  final def occurrencesOf(c: Code)(using env: Env, ctxs: Ctxs): Occurrences = {
    def occOfCase(scrut: Code, matchCase: LabMatchCase)(using env: Env, ctxs0: Ctxs): (Occurrences, Seq[Code]) = {
      val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, matchCase.pattern)
      // Les pattern conditions ne sont pas comptées comme "occurrences"
      val occGuard = occurrencesOf(matchCase.guard)(using env, ctxs1)
      val ctxsRhs = ctxs1.withCond(matchCase.guard)
      val occRhs = occurrencesOf(matchCase.rhs)(using env, ctxsRhs)
      (occGuard ++ occRhs, patConds :+ matchCase.guard)
    }
    def occOfCases(scrut: Code, cases: Seq[LabMatchCase], acc: Occurrences)(using env: Env, ctxs: Ctxs): Occurrences = {
      if (cases.isEmpty) acc
      else {
        val (occCase, caseConds) = occOfCase(scrut, cases.head)
        val negCaseConds = negatedConjunction(caseConds)
        occOfCases(scrut, cases.tail, acc ++ occCase)(using env, ctxs.withCond(negCaseConds))
      }
    }
    def foldOcc(cs: Seq[Code])(using ctxs: Ctxs): (Ctxs, Occurrences) = {
      assert(cs.forall(CodeRes.isTerminal))
      cs.foldLeft((ctxs, Occurrences.empty)) {
        case ((ctxs, acc), c) =>
          given Ctxs = ctxs
          val occC = occurrencesOf(c)
          (ctxs.addBoundDef(c), acc ++ occC)
      }
    }

    if (ctxs.isBoundDef(c)) Occurrences.of(c)
    else if (!CodeRes.isTerminal(c)) {
      val entries = pluggedOccMap.getOrElse((env, c), sys.error("Oh non :("))
      entries.getOrElse(ctxs, {
//        val (prefix, occ) = entries.head // N'importe quelle entry
//        occ.withReplacedPrefix(prefix, ctxs.impureParts)
//        sys.error("Oh non, y a rien :(")
        val teared = tearDown(c)
        val (occ, plugged) = teared.selfPlugged(ctxs)
        occ
      })
    } else {
      code2sig(c) match {
        case Signature(Label.Lit(_), Seq()) => Occurrences.empty
        case Signature(Label.Var(_), Seq()) => Occurrences.of(c)

        case Signature(Label.Application, callee +: args) =>
          assert(CodeRes.isTerminal(callee))
          val occCallee0 = occurrencesOf(callee)
          assert(occCallee0(callee) == Occurrence.Once(ctxs.impureParts, env.nesting, OccurrenceKind.Expanded))
          val occCallee = occCallee0.setTo(callee, Occurrence.Once(ctxs.impureParts, env.nesting, OccurrenceKind.Applied))
          val (ctxs2, occArgs) = foldOcc(args)(using ctxs.addBoundDef(callee))
          Occurrences.of(c)(using env, ctxs2.addBoundDef(c)) ++ occCallee ++ occArgs

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          Occurrences.of(c)(using env, ctxs.addBoundDef(c)) ++ occurrencesOf(body)(using env.incIf(lab), ctxs)

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          Occurrences.of(c)(using env, ctxs.addBoundDef(c)) ++ occurrencesOf(body) ++ occurrencesOf(pred)

        case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
          assert(CodeRes.isTerminal(cond))
          val occCond = occurrencesOf(cond)
          val ctxs1 = ctxs.addBoundDef(cond)
          val occThn = occurrencesOf(thn)(using env, ctxs1.withCond(cond))
          val occEls = occurrencesOf(els)(using env, ctxs1.withNegatedCond(cond))
          Occurrences.of(c)(using env, ctxs1.addBoundDef(c)) ++ occCond ++ occThn ++ occEls

        case Signature(Label.Or, disjs) =>
          disjs.foldLeft((ctxs, Occurrences.of(c)(using env, ctxs.addBoundDef(c)))) {
            case ((ctxs, acc), disj) =>
              given Ctxs = ctxs
              val occDisj = occurrencesOf(disj)
              val tearedDisj = tearDown(disj)
              assert(tearedDisj.ctxs.isLitVarOrBoundDef(tearedDisj.terminal))
              val newCtxs = tearedDisj.ctxs.withNegatedCond(tearedDisj.terminal)
              (newCtxs, acc ++ occDisj)
          }._2

        case Signature(Label.Not, Seq(n)) =>
          val occN = occurrencesOf(n)
          val teared = tearDown(n)
          Occurrences.of(c)(using env, teared.ctxs) ++ occN

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          assert(2 * pats.size == guardRhs.size)
          assert(CodeRes.isTerminal(scrut))
          val cases = pats.zip(guardRhs.grouped(2)).map {
            case (pat, Seq(guard, rhs)) => LabMatchCase(pat, guard, rhs)
            case _ => sys.error("no")
          }
          val occScrut = occurrencesOf(scrut)
          val ctxs1 = ctxs.addBoundDef(scrut)
          occOfCases(scrut, cases, Occurrences.of(c)(using env, ctxs1.addBoundDef(c)) ++ occScrut)(using env, ctxs1)

        case Signature(_, children) =>
          assert(children.forall(CodeRes.isTerminal))
          val (ctxs1, occChildren) = foldOcc(children)
          Occurrences.of(c)(using env, ctxs1.addBoundDef(c)) ++ occChildren
      }
    }
  }

  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  // TODO: Cette histoire de assume(...) en début de lambda????
  final def inlineLambda(outerCtxs: Ctxs, argsSubst: Seq[(VarId, Code)], body: Code)(using env: Env): CodeRes = {
    // Essentiellement un freshener + simplifyTopLvl a chaque step
    object inliner extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)(using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(lab: Label.LambdaLike, Seq(body)) if !ctxs.isBoundDef(c) => // On ne va pas modifier les occurrences liés (c-a-d ce lambda est nécessairement associé à un Let ou va l'être)
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
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Uncoding

  case class RevEnv(revLetDefs: Map[Code, VarId], nesting: LambdaNesting) {
    given env: Env = Env(nesting, false)

    def withLetBounds(vs: Seq[(VarId, Code)]): RevEnv =
      RevEnv(revLetDefs ++ vs.map { case (v, c) => c -> v }.toMap, nesting)

    def withLetBounds(v: VarId, c: Code): RevEnv =
      RevEnv(revLetDefs + (c -> v), nesting)

    def inc: RevEnv = RevEnv(revLetDefs, nesting.inc)

    def incIf(lab: Label.LambdaLike): RevEnv = RevEnv(revLetDefs, nesting.incIf(lab))
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty, LambdaNesting(0))
  }

  case class RevRes(expr: Expr, used: Set[VarId])

  final def uncodeOf(c: Code)(using renv: RevEnv, ctxs: Ctxs): RevRes = {
    import renv.given
    renv.revLetDefs.get(c) match {
      case Some(vIx) =>
        return RevRes(varId2Var(vIx), Set(vIx))
      case None => ()
    }

    code2sig(c) match {
      case Signature(Label.Var(v), Seq()) => RevRes(varId2Var(v), Set(v))
      case Signature(Label.Lit(lit), Seq()) => RevRes(lit, Set.empty)

      case Signature(Label.Let, Seq(cE, cBody)) =>
        val e = uncodeOf(cE)
        val v = freshVarId("bdg", codeTpe(cE))
        val body = uncodeOf(cBody)(using renv.withLetBounds(v, cE), ctxs.addBoundDef(cE))
        RevRes(Let(new ValDef(varId2Var(v)), e.expr, body.expr), e.used ++ body.used)

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        assert(CodeRes.isTerminal(cond))
        val rcond = uncodeOf(cond)
        val ctxs1 = ctxs.addBoundDef(cond)
        val rthn = uncodeOf(thn)(using renv, ctxs1.withCond(cond))
        val rels = uncodeOf(els)(using renv, ctxs1.withNegatedCond(cond))
        RevRes(IfExpr(rcond.expr, rthn.expr, rels.expr), rcond.used ++ rthn.used ++ rels.used)

      case Signature(kind: Label.AssumeLike, Seq(pred, body)) => uncodeOfAssumeLike(kind, pred, body)

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        val rbody = uncodeOf(body)
        val rpred = uncodeOf(pred)
        val predLam = rpred.expr match {
          case lam@Lambda(_, _) => lam
          case Let(v, lam@Lambda(_, _), predBody) if predBody == v.toVariable => lam // TODO: Slmt pour debug fnPurity
        }
        RevRes(Ensuring(rbody.expr, predLam), rbody.used ++ rpred.used)

      case Signature(kind: Label.LambdaLike, Seq(body)) => uncodeOfLambdaLike(kind, body)

      case Signature(Label.Or, disjs) =>
        val rdisjs = foldLeftDisjunction(disjs, Seq.empty[RevRes])((acc, disj) => acc :+ uncodeOf(disj))
        RevRes(Or(rdisjs.map(_.expr)), rdisjs.flatMap(_.used).toSet)

      case Signature(Label.Not, Seq(c)) => uncodeOfNot(c)

      case Signature(Label.MatchExpr(pats), cScrut +: cGuardRhs) =>
        assert(2 * pats.size == cGuardRhs.size)
        val (guards, rhss) = cGuardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val cases = pats.zip(guards).zip(rhss).map {
          case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
        }
        val rscrut = uncodeOf(cScrut)
        val (rcases, used) = uncodeOfCases(cScrut, cases, Seq.empty, rscrut.used)(using renv, ctxs.addBoundDef(cScrut))
        RevRes(MatchExpr(rscrut.expr, rcases), used)

      case Signature(Label.Tuple, args) => uncodeOfArgs(args)(Tuple.apply)
      case Signature(Label.ADT(id, tps), args) => uncodeOfArgs(args)(ADT(id, tps, _))
      case Signature(Label.ADTSelector(_, _, sel), Seq(recv)) => uncodeOfArgs(recv)(ADTSelector(_, sel))
      case Signature(Label.FunctionInvocation(id, tps), args) => uncodeOfArgs(args)(FunctionInvocation(id, tps, _))
      case Signature(Label.Annotated(flags), Seq(e)) => uncodeOfArgs(e)(Annotated(_, flags))
      case Signature(Label.IsConstructor(_, id), Seq(e)) => uncodeOfArgs(e)(IsConstructor(_, id))
      case Signature(Label.Application, calleeAndArgs) =>
        uncodeOfArgs(calleeAndArgs) { case callee +: args => Application(callee, args) }

      case Signature(Label.Equals, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(Equals.apply)
      case Signature(Label.LessThan, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(LessThan.apply)
      case Signature(Label.GreaterThan, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(GreaterThan.apply)
      case Signature(Label.LessEquals, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(LessEquals.apply)
      case Signature(Label.GreaterEquals, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(GreaterEquals.apply)
      case Signature(Label.UMinus, Seq(c)) => uncodeOfArgs(c)(UMinus.apply)

      case Signature(lab@(Label.Plus | Label.Times), terms) =>
        assert(terms.size >= 2)
        val recons: (Expr, Expr) => Expr = if (lab == Label.Plus) Plus.apply else Times.apply
        uncodeOfArgs(terms) { case init :+ e1 :+ e2 =>
          init.foldRight(recons(e1, e2))(recons)
        }

      case Signature(Label.Minus, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(Minus.apply)
      case Signature(Label.Division, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(Division.apply)
      case Signature(Label.Remainder, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(Remainder.apply)
      case Signature(Label.Modulo, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(Modulo.apply)
      case Signature(Label.BVNot, Seq(c)) => uncodeOfArgs(c)(BVNot.apply)
      case Signature(Label.BVAnd, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVAnd.apply)
      case Signature(Label.BVOr, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVOr.apply)
      case Signature(Label.BVXor, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVXor.apply)
      case Signature(Label.BVShiftLeft, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVShiftLeft.apply)
      case Signature(Label.BVAShiftRight, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVAShiftRight.apply)
      case Signature(Label.BVLShiftRight, Seq(c1, c2)) => uncodeOfArgs(c1, c2)(BVLShiftRight.apply)
      case Signature(Label.BVNarrowingCast(newType), Seq(c)) => uncodeOfArgs(c)(BVNarrowingCast(_, newType))
      case Signature(Label.BVWideningCast(newType), Seq(c)) => uncodeOfArgs(c)(BVWideningCast(_, newType))
      case Signature(Label.BVUnsignedToSigned, Seq(c)) => uncodeOfArgs(c)(BVUnsignedToSigned.apply)
      case Signature(Label.BVSignedToUnsigned, Seq(c)) => uncodeOfArgs(c)(BVSignedToUnsigned.apply)
      case Signature(Label.TupleSelect(index), Seq(c)) => uncodeOfArgs(c)(TupleSelect(_, index))

      case Signature(Label.FiniteSet(base), args) => uncodeOfArgs(args)(FiniteSet(_, base))
      case Signature(Label.SetAdd, Seq(set, elem)) => uncodeOfArgs(set, elem)(SetAdd.apply)
      case Signature(Label.ElementOfSet, Seq(elem, set)) => uncodeOfArgs(elem, set)(ElementOfSet.apply)
      case Signature(Label.SubsetOf, Seq(lhs, rhs)) => uncodeOfArgs(lhs, rhs)(SubsetOf.apply)
      case Signature(Label.SetIntersection, Seq(lhs, rhs)) => uncodeOfArgs(lhs, rhs)(SetIntersection.apply)
      case Signature(Label.SetUnion, Seq(lhs, rhs)) => uncodeOfArgs(lhs, rhs)(SetUnion.apply)
      case Signature(Label.SetDifference, Seq(lhs, rhs)) => uncodeOfArgs(lhs, rhs)(SetDifference.apply)

      case Signature(Label.FiniteArray(base), args) => uncodeOfArgs(args)(FiniteArray(_, base))
      case Signature(Label.LargeArray(elemsIndices, base), all) =>
        uncodeOfArgs(all) { case elems :+ default :+ size =>
          LargeArray(elemsIndices.zip(elems).toMap, default, size, base)
        }
      case Signature(Label.ArraySelect, Seq(arr, i)) => uncodeOfArgs(arr, i)(ArraySelect.apply)
      case Signature(Label.ArrayUpdated, Seq(arr, i, v)) => uncodeOfArgs(arr, i, v)(ArrayUpdated.apply)
      case Signature(Label.ArrayLength, Seq(arr)) => uncodeOfArgs(arr)(ArrayLength.apply)

      case Signature(Label.FiniteMap(keyTpe, valueTpe), elems :+ default) =>
        assert(elems.size % 2 == 0)
        uncodeOfArgs(elems :+ default) { case exprElems :+ exprDefault =>
          val paired = exprElems.grouped(2).map { case Seq(k, v) => (k, v) }.toSeq
          FiniteMap(paired, exprDefault, keyTpe, valueTpe)
        }
      case Signature(Label.MapApply, Seq(map, k)) => uncodeOfArgs(map, k)(MapApply.apply)
      case Signature(Label.MapUpdated, Seq(map, k, v)) => uncodeOfArgs(map, k, v)(MapUpdated.apply)

      case Signature(Label.Error(tpe, descr), Seq()) => RevRes(Error(tpe, descr), Set.empty)
      case Signature(Label.NoTree(tpe), Seq()) => RevRes(NoTree(tpe), Set.empty)

      case sig => sys.error(s"uncodeOf: what is this: $sig")
    }
  }

  final def convertPattern(scrut: Code, pat: LabelledPattern, vds: Map[Code, ValDef]): Pattern = {
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
        val rsubs = recHelper(adtSubScrutinees(scrut, ADTType(id, tps)), subps)
        ADTPattern(bdg, id, tps, rsubs)
      case LabelledPattern.TuplePattern(subps) =>
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val rsubs = recHelper(tupleSubscrutinees(scrut, tt), subps)
        TuplePattern(bdg, rsubs)
      case LabelledPattern.Lit(lit) => LiteralPattern(bdg, lit)
      case LabelledPattern.Unapply(recs, id, tps, subps) =>
        assert(recs.isEmpty)
        val rsubs = recHelper(unapplySubScrutinees(scrut, id, tps).subs, subps)
        UnapplyPattern(bdg, Seq.empty, id, tps, rsubs)
    }
  }

  case class UncodedCase(pat: Pattern, guard: RevRes, rhs: RevRes, caseConds: Seq[Code])

  final def uncodeOfCase(cScrut: Code, cse: LabMatchCase)(using renv0: RevEnv, ctxs0: Ctxs): UncodedCase = {
    import renv0.given
    val PatBdgsAndConds(ctxs1, allScruts, patConds) = addPatternBindingsAndConds(ctxs0, cScrut, cse.pattern)
    val scrutBdgs = allScruts.zipWithIndex.map {
      case (subScrut, i) =>
        val vId = idOfVariable(Variable.fresh(s"bdg$i", codeTpe(subScrut)))
        vId -> subScrut
    }
    val renv1 = renv0.withLetBounds(scrutBdgs)
    val rguard = uncodeOf(cse.guard)(using renv1, ctxs1)
    val ctxsForRhs = ctxs1.withCond(cse.guard)
    val rrhs = uncodeOf(cse.rhs)(using renv1, ctxsForRhs)
    // On retire les scrut. binding qui sont inutiles.
    val scrutVds = scrutBdgs.filter { case (v, _) => rguard.used(v) || rrhs.used(v) }
      .map { case (v, c) =>
        val vd = new ValDef(varId2Var(v))
        c -> vd
      }.toMap
    val convertedPattern = convertPattern(cScrut, cse.pattern, scrutVds)
    UncodedCase(convertedPattern, rguard, rrhs, patConds :+ cse.guard)
  }

  final def uncodeOfCases(cScrut: Code, cases: Seq[LabMatchCase], transformedCases: Seq[MatchCase], used: Set[VarId])
                         (using renv: RevEnv, ctxs: Ctxs): (Seq[MatchCase], Set[VarId]) = {
    import renv.given
    cases match {
      case Seq() => (transformedCases, used)
      case cse +: rest =>
        val uncoded = uncodeOfCase(cScrut, cse)
        val negCaseConds = negatedConjunction(uncoded.caseConds)
        val theGuard =
          if (uncoded.guard.expr == BooleanLiteral(true)) None
          else Some(uncoded.guard.expr)
        val theCase = MatchCase(uncoded.pat, theGuard, uncoded.rhs.expr)
        val newUsed = used ++ uncoded.guard.used ++ uncoded.rhs.used
        uncodeOfCases(cScrut, rest, transformedCases :+ theCase, newUsed)(using renv, ctxs.withCond(negCaseConds))
    }
  }

  final def uncodeOfLambdaLike(kind: Label.LambdaLike, body: Code)(using renv: RevEnv, ctxs: Ctxs): RevRes = {
    val rbody = uncodeOf(body)(using renv.incIf(kind), ctxs)
    kind match {
      case Label.Lambda(params) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        RevRes(Lambda(vds, rbody.expr), rbody.used)
      case Label.Choose(v) =>
        RevRes(Choose(new ValDef(varId2Var(v)), rbody.expr), rbody.used)
      case Label.Forall(params) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        RevRes(Forall(vds, rbody.expr), rbody.used)
    }
  }

  final def uncodeOfAssumeLike(kind: Label.AssumeLike, pred: Code, body: Code)(using renv: RevEnv, ctxs: Ctxs): RevRes = {
    import renv.given
    assert(CodeRes.isTerminal(pred))
    val rpred = uncodeOf(pred)
    val rbody = uncodeOf(body)(using renv, ctxs.addBoundDef(pred).withAssumeLike(kind, pred))
    val expr = kind match {
      case Label.Assume => Assume(rpred.expr, rbody.expr)
      case Label.Assert => Assert(rpred.expr, None, rbody.expr)
      case Label.Require => Require(rpred.expr, rbody.expr)
      case Label.Decreases => Decreases(rpred.expr, rbody.expr)
    }
    RevRes(expr, rpred.used ++ rbody.used)
  }

  final def uncodeOfNot(c: Code)(using renv: RevEnv, ctxs: Ctxs): RevRes = {
    import renv.given

    def mayRmNeg(op: Code)(using Ctxs): Boolean = {
      def isSimple(c: Code): Boolean = isLitOrVar(c) || renv.revLetDefs.contains(c)
      // TODO: Dire pk ! pour le op: car s'il est bind, une inversion risque de dupliquer les operandes
      def mayRm(operands: Seq[Code]): Boolean = operands.forall(isSimple) || !renv.revLetDefs.contains(op)

      code2sig(op) match {
        case Signature(Label.Not, Seq(cc)) => mayRm(Seq(cc))
        case Signature(Label.GreaterThan | Label.GreaterEquals |
                       Label.LessThan | Label.LessEquals, Seq(lhs, rhs)) => mayRm(Seq(lhs, rhs))
        case _ => true
      }
    }

    code2sig(c) match {
      case Signature(Label.Or, disjs) =>
        val negDisjs = disjs.foldLeft((Seq.empty[RevRes], ctxs)) {
          case ((acc, ctxs), disj) =>
            given Ctxs = ctxs
            val negCr = negCodeResOf(disj)(mayRmNeg)
            val (_, negPlugged) = negCr.selfPlugged(ctxs)
            val negExpr = uncodeOf(negPlugged)
            // Comme on est en négation, pour le next ctxs, on souhaite avoir ctxs avec comme bounddef la négation
            // du terminal de disj et comme condition le terminal de disj
            (acc :+ negExpr, negCr.ctxs.withNegatedCond(negCr.terminal))
        }._1
        RevRes(And(negDisjs.map(_.expr)), negDisjs.flatMap(_.used).toSet)

      case _ =>
        val rc = uncodeOf(c)
        RevRes(Not(rc.expr), rc.used)
    }
  }

  final def uncodeOfArgs(args: Seq[Code])(recons: Seq[Expr] => Expr)(using renv: RevEnv, ctxs: Ctxs): RevRes = {
    import renv.given
    val rargs = args.foldLeft((Seq.empty[RevRes], ctxs)) {
      case ((acc, ctxs), arg) =>
        given Ctxs = ctxs
        assert(CodeRes.isTerminal(arg))
        val res = uncodeOf(arg)
        (acc :+ res, ctxs.addBoundDef(arg))
    }._1
    RevRes(recons(rargs.map(_.expr)), rargs.flatMap(_.used).toSet)
  }

  final def uncodeOfArgs(c1: Code)(recons: Expr => Expr)(using RevEnv, Ctxs): RevRes =
    uncodeOfArgs(Seq(c1)) { case Seq(e1) => recons(e1) }

  final def uncodeOfArgs(c1: Code, c2: Code)(recons: (Expr, Expr) => Expr)(using RevEnv, Ctxs): RevRes =
    uncodeOfArgs(Seq(c1, c2)) { case Seq(e1, e2) => recons(e1, e2) }

  final def uncodeOfArgs(c1: Code, c2: Code, c3: Code)(recons: (Expr, Expr, Expr) => Expr)(using RevEnv, Ctxs): RevRes =
    uncodeOfArgs(Seq(c1, c2, c3)) { case Seq(e1, e2, e3) => recons(e1, e2, e3) }

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Code transformer & folder

  // TODO: Commentaire à propos de code potentiel dans les labels qui ne sont pas transform
  // TODO: Devrait-on run simplifyDisj ou simplifyTopLvlSig à chaque step?
  trait CodeTransformer {
    type Extra

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = {
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

    def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = {
      val tpe = codeTpe(c)
      assert(!repl.contains(c), s"$c = ${code2sig(c)} n'a pas été remplacé par transform")

      code2sig(c) match {
        case Signature(Label.Var(_) | Label.Lit(_), Seq()) => CodeRes(c, ctxs)

        case Signature(Label.Let, Seq(e, b)) if ctxs.isBoundDef(e) =>
          transform(b, repl, extra)

        case Signature(Label.Let, Seq(e, b)) =>
          assert(CodeRes.isTerminal(e))
          assert(!isLitOrVar(e))
          val re = transform(e, repl, extra)
          assert(re.ctxs.isLitVarOrBoundDef(re.terminal))
          transform(b, repl + (e -> re.terminal), extra)(using env, re.ctxs)

        case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
          assert(CodeRes.isTerminal(cond))
          val rcond = transform(cond, repl, extra)
          val thennCtxs = rcond.ctxs.withCond(rcond.terminal)
          val rthenn = transform(thenn, repl, extra)(using env, thennCtxs)
          val elsCtxs = rcond.ctxs.withNegatedCond(rcond.terminal)
          val rels = transform(els, repl, extra)(using env, elsCtxs)
          CodeRes.ifExpr(rcond, rthenn, rels, tpe)

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val rbody = transform(body, repl, extra)(using env.incIf(lab))
          CodeRes.lambdaLike(lab, rbody, tpe)

        case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
          assert(CodeRes.isTerminal(pred))
          val rpred = transform(pred, repl, extra)
          assert(rpred.ctxs.isLitVarOrBoundDef(rpred.terminal))
          transform(body, repl, extra)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal))

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          val rbody = transform(body, repl, extra)
          val rpred = transform(pred, repl, extra)
          CodeRes.ensuring(rbody, rpred, tpe)

        case Signature(Label.Or, disjs) =>
          transformDisjunction(disjs)(transform(_, repl, extra))

        case Signature(Label.Not, Seq(n)) =>
          val rn = transform(n, repl, extra)
          rn.derived(negCodeOf(rn.terminal))

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
          val rcases = transformCases(scrut, rscrut.terminal, cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using env, rscrut.ctxs)
          CodeRes.matchExpr(rscrut, rcases, tpe)

        // TODO: Que pour les cas triviaux où env est le même, bindings std, etc.
        case Signature(lab, children) => transformSeq(children, tpe, repl, extra)(Signature(lab, _))
      }
    }

    final def transformSeq(cs: Seq[Code], tpe: Type, repl: Map[Code, Code], extra: Extra)
                          (mkSig: Seq[Code] => Signature)(using env: Env, ctxs: Ctxs): CodeRes = {
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

    def transformCase(oldScrut: Code, newScrut: Code, matchCase: LabMatchCase, repl0: Map[Code, Code], extra: Extra)
                     (using env: Env, ctxs0: Ctxs): (CodeResMatchCase, Seq[Code]) = {
      assert(repl0.get(oldScrut) == Some(newScrut), s"'repl0' ne contient pas $oldScrut -> $newScrut")
      assert(ctxs0.isLitVarOrBoundDef(newScrut))

      val PatBdgsAndConds(ctxs1, newBdgs, patConds) = addPatternBindingsAndConds(ctxs0, newScrut, matchCase.pattern)
      val repl = {
        if (oldScrut == newScrut) repl0
        else {
          val PatBdgsAndConds(_, oldBdgs, _) = addPatternBindingsAndConds(ctxs0.addBoundDef(oldScrut), oldScrut, matchCase.pattern)
          assert(oldBdgs.size == newBdgs.size)
          repl0 ++ oldBdgs.zip(newBdgs).toMap
        }
      }

      val rguard = transform(matchCase.guard, repl, extra)(using env, ctxs1)
      val (compGuard, cGuard) = rguard.selfPlugged(ctxs1)

      val ctxsForRhs = ctxs1.withCond(cGuard)
      val rrhs = transform(matchCase.rhs, repl, extra)(using env, ctxsForRhs)
      val (compRhs, cRhs) = rrhs.selfPlugged(ctxsForRhs)

      val newMatchCase = LabMatchCase(matchCase.pattern, cGuard, cRhs)
      (CodeResMatchCase(newMatchCase, compGuard ++ compRhs), patConds :+ cGuard)
    }

    def transformCases(oldScrut: Code, newScrut: Code, cases: Seq[LabMatchCase],
                       repl: Map[Code, Code], extra: Extra,
                       acc: Seq[CodeResMatchCase])
                      (using env: Env, ctxs: Ctxs): Seq[CodeResMatchCase] = {
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

    final def tryFold(c: Code, acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, T] =
      tryFoldImpl(c, acc, extra)

    def tryFoldImpl(c: Code, acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, T] = code2sig(c) match {
      case Signature(Label.Lit(_) | Label.Var(_), Seq()) => Right(acc)

      case Signature(Label.Let, Seq(e, b)) if ctxs.isBoundDef(e) =>
        tryFold(b, acc, extra)

      case Signature(Label.Let, Seq(e, b)) =>
        assert(CodeRes.isTerminal(e))
        assert(!isLitOrVar(e))
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
          rels <- tryFold(els, rthn, extra)(using env, ctxs1.withNegatedCond(cond))
        } yield rels

      case Signature(Label.Or, disjs) =>
        ocbsl.tryFoldLeftDisjunction(disjs, acc)((acc, disj) => tryFold(disj, acc, extra))

      case Signature(Label.Not, Seq(n)) =>
        tryFold(n, acc, extra)

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        for {
          rbody <- tryFold(body, acc, extra)
          rpred <- tryFold(pred, rbody, extra)
        } yield rpred

      case Signature(lab: Label.LambdaLike, Seq(body)) =>
        tryFold(body, acc, extra)(using env.incIf(lab), ctxs)

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
      case Signature(_, args) =>
        assert(args.forall(CodeRes.isTerminal))
        tryFoldArgs(args, acc, extra)
    }

    final def tryFoldArgs(args: Seq[Code], acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, T] = {
      ocbsl.tryFoldLeft(args, (acc, ctxs)) {
        case ((acc, ctxs), arg) =>
          given Ctxs = ctxs
          assert(CodeRes.isTerminal(arg))
          tryFold(arg, acc, extra)
            .map(newAcc => (newAcc, ctxs.addBoundDef(arg)))
      }.map(_._1)
    }

    final def tryFoldCase(scrut: Code, matchCase: LabMatchCase, acc: T, extra: Extra)
                         (using env: Env, ctxs0: Ctxs): Either[E, (T, Seq[Code])] = {
      val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, matchCase.pattern)
      for {
        // TODO: Ok? Après tout, ctxs1 contient les binding et les conds!!!
        // TODO: ou alors: pure sauf s'il y a des unapply, dans ce cas on check fnpurity des unapply
        rpatConds <- tryFoldPatternConditions(patConds, acc, extra)(using env, ctxs1)
        rguard <- tryFold(matchCase.guard, rpatConds, extra)(using env, ctxs1)
        ctxsForRhs = ctxs1.withCond(matchCase.guard)
        rrhs <- tryFold(matchCase.rhs, rguard, extra)(using env, ctxsForRhs)
      } yield (rrhs, patConds :+ matchCase.guard)
    }

    final def tryFoldCases(scrut: Code, cases: Seq[LabMatchCase], acc: T, extra: Extra)
                    (using env: Env, ctxs: Ctxs): Either[E, T] = {
      if (cases.isEmpty) Right(acc)
      else {
        tryFoldCase(scrut, cases.head, acc, extra).flatMap {
          case (rcase, caseConds) =>
            val negCaseConds = negatedConjunction(caseConds)
            tryFoldCases(scrut, cases.tail, rcase, extra)(using env, ctxs.withCond(negCaseConds))
        }
      }
    }

    def tryFoldPatternConditions(patConds: Seq[Code], acc: T, extra: Extra)(using Env, Ctxs): Either[E, T]
  }

  final def tearDown(c: Code)(using env: Env, ctxs: Ctxs): CodeRes = {
    object tear extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(Label.Or, first +: _) =>
          val firstTeared = transform(first, repl, ())
          CodeRes(c, firstTeared.ctxs.addBoundDef(c))
        case Signature(Label.IfExpr, Seq(cond, _, _)) =>
          val condTeared = transform(cond, repl, ())
          CodeRes(c, condTeared.ctxs.addBoundDef(c))
        case Signature(_: (Label.Ensuring.type | Label.LambdaLike), _) => CodeRes(c, ctxs.addBoundDef(c))
        case Signature(Label.MatchExpr(_), scrut +: _) =>
          val scrutTeared = transform(scrut, repl, ())
          CodeRes(c, scrutTeared.ctxs.addBoundDef(c))
        case _ => super.transformImpl(c, repl, ())
      }
    }

    if (CodeRes.isTerminal(c)) CodeRes(c, ctxs.addBoundDef(c))
    else {
      unplugged(c).map(_._1)
        .getOrElse(tear.transform(c, Map.empty, ()))
    }
  }

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Match expression utilities

  final def tupleSubscrutinees(scrut: Code, tt: TupleType): Seq[Code] = {
    tt.bases.zipWithIndex.map { case (base, i) => tupleSelect(scrut, i + 1, base) }
  }

  final def adtSubScrutinees(scrut: Code, adt: ADTType): Seq[Code] = {
    val tcons = getConstructor(adt.id, adt.tps)
    tcons.fields.map(fld => adtSelect(scrut, Label.ADTSelector(adt, tcons, fld.id), fld.getType))
  }

  final def adtMatchCond(scrut: Code, adt: ADTType)(using Env, Ctxs): Code = {
    isConstructor(scrut, adt, adt.id) match {
      case Some(true) => trueCode
      case Some(false) => falseCode
      case None => codeOfSig(mkIsCtor(scrut, adt, adt.id), BoolTy)
    }
  }

  case class UnapplySubScruts(unapplyInvoc: Code, getInvoc: Code, subs: Seq[Code], patCond: Code)

  final def unapplySubScrutinees(scrut: Code, id: Identifier, tps: Seq[Type]): UnapplySubScruts = {
    val fdUnapply = getFunction(id, tps)
    val unapplyInvocSig = mkFunInvoc(id, tps, Seq(scrut))
    val unapplyInvoc = codeOfSig(unapplyInvocSig, fdUnapply.returnType)

    // The accessor in question is either get or isEmpty so fnId = get or isEmpty
    // En gros: get(unapplyInvoc) ou isEmpty(unapplyInvoc) en fonction de ce qu'on passe pour fnId
    // See Expression#UnapplyPattern
    def unapplyAccessor(fnId: Identifier): Code = {
      val fdAcc = getFunction(fnId)
      assert(fdAcc.params.size == 1)
      val tpMap = instantiation(fdAcc.params.head.tpe, fdUnapply.returnType)
        .getOrElse(sys.error("Unapply pattern failed type instantiation"))
      val typedFd = fdAcc.typed(fdAcc.typeArgs map tpMap)

      val accInvocSig = mkFunInvoc(typedFd.id, typedFd.tps, Seq(unapplyInvoc))
      codeOfSig(accInvocSig, typedFd.returnType)
    }

    val isUnapplyFlag = fdUnapply.flags.collectFirst {
      case f@IsUnapply(_, _) => f
    }.getOrElse(sys.error("Oh non, on nous a menti encore une fois :("))

    val getInvoc = unapplyAccessor(isUnapplyFlag.get)
    val isEmptyInvoc = unapplyAccessor(isUnapplyFlag.isEmpty)
    val nonEmpty = codeOfSig(mkNot(isEmptyInvoc), BoolTy)

    codeTpe(getInvoc) match {
      case tt@TupleType(_) =>
        val subs = tupleSubscrutinees(getInvoc, tt)
        UnapplySubScruts(unapplyInvoc, getInvoc, subs, nonEmpty)
      case _ =>
        // The subpattern is getInvoc itself, as we don't need to de-structure it into a tuple
        UnapplySubScruts(unapplyInvoc, getInvoc, Seq(getInvoc), nonEmpty)
    }
  }

  case class PatBdgsAndConds(ctxs: Ctxs, bdgs: Seq[Code], patConds: Seq[Code])

  final def addPatternBindingsAndConds(ctxs: Ctxs, scrut: Code, pat: LabelledPattern)(using env: Env): PatBdgsAndConds = {
    def recHelper(ctxs: Ctxs, subscruts: Seq[Code], subps: Seq[LabelledPattern]): PatBdgsAndConds = {
      assert(subscruts.size == subps.size)
      subscruts.zip(subps).foldLeft(PatBdgsAndConds(ctxs, Seq.empty[Code], Seq.empty[Code])) {
        case (PatBdgsAndConds(ctxs, bdgsAcc, condsAcc), (subscrut, subpat)) =>
          val PatBdgsAndConds(ctxs2, bdgs2, conds2) = addPatternBindingsAndConds(ctxs.addBoundDef(subscrut), subscrut, subpat)
          PatBdgsAndConds(ctxs2, bdgsAcc ++ bdgs2, condsAcc ++ conds2)
      }
    }

    assert(ctxs.isLitVarOrBoundDef(scrut))
    pat match {
      case LabelledPattern.Wildcard | LabelledPattern.Lit(_) => PatBdgsAndConds(ctxs, Seq.empty, Seq.empty)

      case LabelledPattern.ADT(id, tps, subps) =>
        val subscruts = adtSubScrutinees(scrut, ADTType(id, tps))
        val adtPatCond = adtMatchCond(scrut, ADTType(id, tps))(using env, ctxs)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs, subscruts, subps)
        assert(ctxs.isPrefixOf(newCtxs))
        PatBdgsAndConds(newCtxs, subscruts ++ recBdgs, adtPatCond +: recPatConds)

      case LabelledPattern.TuplePattern(subps) =>
        val tt@TupleType(bases) = codeTpe(scrut)
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs, subscruts, subps)
        assert(ctxs.isPrefixOf(newCtxs))
        PatBdgsAndConds(newCtxs, subscruts ++ recBdgs, recPatConds)

      case LabelledPattern.Unapply(recs, id, tps, subps) =>
        assert(recs.isEmpty)
        val unapp = unapplySubScrutinees(scrut, id, tps)
        // 1. On bind unapply(scrut): Option[...]
        // 2. On s'assure à ce que l'Option retourné est un Some (avec unapp.patCond)
        // 3. On bind unapply(scrut).get
        val ctxs2 = ctxs.addBoundDef(unapp.unapplyInvoc)
          .withCond(unapp.patCond)
          .addBoundDef(unapp.getInvoc)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs2, unapp.subs, subps)
        assert(ctxs.isPrefixOf(newCtxs))

        val theseBdgs =
          if (unapp.subs == Seq(unapp.getInvoc)) Seq(unapp.patCond, unapp.getInvoc) // pour éviter d'avoir 2x unapp.getInvoc dans les subs
          else Seq(unapp.patCond, unapp.getInvoc) ++ unapp.subs

        PatBdgsAndConds(newCtxs, theseBdgs ++ recBdgs, unapp.patCond +: recPatConds)
    }
  }

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Misc

  object IntLikeLitSig {
    def unapply(sig: Signature): Option[BigInt] = sig match {
      case Signature(Label.Lit(bv@BVLiteral(_, _, _)), _) => Some(bv.toBigInt)
      case Signature(Label.Lit(IntegerLiteral(v)), _) => Some(v)
      case _ => None
    }
  }

  object BoolLitSig {
    def unapply(sig: Signature): Option[Boolean] = sig match {
      case Signature(Label.Lit(BooleanLiteral(b)), _) => Some(b)
      case _ => None
    }
  }

  object EqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.Equals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object LeqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.LessEquals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object LtSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.LessThan, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object GeqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.GreaterEquals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object GtSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.GreaterThan, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  final def isPrefixOf[T](lhs: Seq[T], rhs: Seq[T]): Boolean =
    lhs.size <= rhs.size && lhs.zip(rhs).forall { case (l, r) => l == r }

  final def findMap[A, B](as: Seq[A])(f: A => Option[B]): Option[B] =
    if (as.isEmpty) None
    else f(as.head).orElse(findMap(as.tail)(f))

  final def addIfAbsent[K, V](map: Map[K, V])(kv: (K, V)): Map[K, V] =
    if (map.contains(kv._1)) map else map + kv

  final def tryFoldLeft[E, A, T](as: Seq[A], init: T)(f: (T, A) => Either[E, T]): Either[E, T] = {
    def rec(as: Seq[A], acc: T): Either[E, T] = as match {
      case Seq() => Right(acc)
      case head +: tail => f(acc, head) match {
        case Left(e) => Left(e)
        case Right(newAcc) => rec(tail, newAcc)
      }
    }
    rec(as, init)
  }

  // Is `c` an ADT with constructor `id`?
  //   Some(true) - Yes
  //   Some(false) - No
  //   None - Can't tell
  final def isConstructor(c: Code, adt: ADTType, id: Identifier)(using Env, Ctxs): Option[Boolean] = {
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

  final def idOfVariable(v: Variable): VarId = var2VarId.get(v) match {
    case Some(vId) => vId
    case None =>
      val vId = VarId.fromInt(varIdCounter)
      varIdCounter += 1
      var2VarId += v -> vId
      varId2Var += vId -> v
      vId
  }

  final inline def code2sig(c: Code): Signature = code2sigMap(c)

  final inline def codeTpe(c: Code): Type = codeTpeMap(c)

  final def freshened(v: VarId): VarId = idOfVariable(varId2Var(v).freshen)

  final def freshVarId(name: String, tpe: Type): VarId = idOfVariable(Variable.fresh(name, tpe))

  final def codeOfSig(sig: Signature, tpe: Type): Code = {
    sig2codeMap.get(sig) match {
      case Some(c) =>
        assert(codeTpeMap(c) == tpe, s"${codeTpeMap(c)} != $tpe")
        c
      case None =>
        val newCode = Code.fromInt(sig2codeMap.size)
        assert(!code2sigMap.contains(newCode))
        sig2codeMap += sig -> newCode
        code2sigMap += newCode -> sig
        codeTpeMap += newCode -> tpe
        newCode
    }
  }

  final def varTpe(v: VarId): Type = varId2Var(v).getType // TODO: Apparemment, il y a une difference entre .getType et .tpe (pour les refinement type)

  final def codeOfIntLit(lit: BigInt, tpe: Type): Code = codeOfLit(intLitOfType(lit, tpe))

  final def intLitOfType(lit: BigInt, tpe: Type): Literal[_] = tpe match {
    case IntegerType() => IntegerLiteral(lit)
    case RealType() => FractionLiteral(lit, 1)
    case BVType(signed, size) =>
      // BVLiteral guards against signed=true and lit < 0, but not against lit not fitting
      // into the given bitwidth (it wrap-around)
      val (loIncl, hiExcl) = {
        if (signed) (-BigInt(2).pow(size - 1), BigInt(2).pow(size - 1))
        else (BigInt(0), BigInt(2).pow(size))
      }
      if (!(loIncl <= lit && lit < hiExcl)) {
        sys.error(s"$lit does not fit into $tpe  (with range [$loIncl, $hiExcl[)")
      }
      BVLiteral(signed, lit, size)
    case _ => sys.error(s"$tpe is not an integer-like type")
  }

  final def codeOfVarId(v: VarId): Code = codeOfSig(mkVar(v), varTpe(v))

  final def codeOfLit[T](l: Literal[T]): Code = codeOfSig(mkLit(l), l.getType)

  final def isLambda(c: Code): Boolean = code2sig(c).label.isLambda

  final def isLambdaLike(c: Code): Boolean = code2sig(c).label.isLambdaLike

  final def isVar(c: Code): Boolean = code2sig(c).label.isVar

  final def isLit(c: Code): Boolean = code2sig(c).label.isLiteral

  final def isLitOrVar(c: Code): Boolean = code2sig(c).label.isLitOrVar

  final def b2c(b: Boolean): Code = if (b) trueCode else falseCode

  final def b2sig(b: Boolean): Signature = if (b) trueSig else falseSig

  final val assmChkPurity: Purity = if (opts.assumeChecked) Pure else Impure

  final def unAnd(e: Expr): Seq[Expr] = e match {
    case And(es) => es.flatMap(unAnd)
    case e => Seq(e)
  }

  final def unOr(e: Expr): Seq[Expr] = e match {
    case Or(es) => es.flatMap(unOr)
    case e => Seq(e)
  }

  final def unOrCodes(disjs: Seq[Code]): Seq[Code] = disjs.flatMap(unOrCode)

  final def unOrCode(c: Code): Seq[Code] = code2sig(c) match {
    case Signature(Label.Or, disjs) => disjs.flatMap(unOrCode)
    case _ => Seq(c)
  }

  // Map all codes to their corresponding signatures (for debugging purposes)

  case class ExplicitSig(label: Label, children: Seq[ExplicitSig]) {
    override def toString: String = {
      if (children.isEmpty) label.toString
      else s"($label, ${children.mkString(", ")})"
    }
  }

  final def asExplicitSig(c: Code): ExplicitSig = {
    val sig = code2sig(c)
    ExplicitSig(sig.label, sig.children.map(asExplicitSig))
  }
  //endregion
}
