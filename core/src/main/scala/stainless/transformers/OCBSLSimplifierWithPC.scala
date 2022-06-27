package stainless
package transformers

trait OCBSLSimplifierWithPC extends Transformer with stainless.transformers.SimplifierWithPC {
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

  override val pp: PathProvider[Env] = Env

  import OCBSL.{given, _}

  private val ocbslTL = ThreadLocal.withInitial(() => new OCBSL)
  private def ocbsl = ocbslTL.get()

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    given Subst = path.mkSubst
    val oc = ocbsl
    val code = oc.codeOf(e)
    /*
    val simpE = oc.uncodeOf(code).copiedFrom(e)
    (simpE, oc.codePurity(code).isPure)
    */
    ???
  }

  case class Env(conditions: Set[Code],
                 exprSubst: Map[Variable, Expr],
                 exprCode: Map[Variable, Code],
                 // Note: Order is important (hence Seq)
                 bound: Seq[ValDef]) extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = p match {
      // TODO: Qq binding ajouté
      // TODO: Pk n'ajoute-t-on pas tous les bdgs?
      //  ~> p-e parce que le Let case n'exploite pas ces infos?
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda | _: FiniteArray | _: LargeArray)) =>
        // TODO: Quid purity???
        val c = ocbsl.codeOf(expr)(using mkSubst)
        Env(conditions, exprSubst + (vd.toVariable -> expr), exprCode + (vd.toVariable -> c), bound)
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) {
          val c = ocbsl.codeOf(exp)(using mkSubst)
          Env(conditions, exprSubst + (vd.toVariable -> exp), exprCode + (vd.toVariable -> c), bound)
        } else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = Env(conditions, exprSubst, exprCode, bound :+ vd)

    // TODO: On pourra supposer que cond a été simplifié avant
    override def withCond(cond: Expr): Env = {
      // TODO: Et si cond est impure???
      val codeCond = ocbsl.codeOf(cond)(using mkSubst)
      Env(conditions + codeCond, exprSubst, exprCode, bound)
    }

    override def negate: Env = {
      given Subst = mkSubst
      Env(Set(ocbsl.negatedConjunction(conditions)), exprSubst, exprCode, bound)
    }

    override def merge(that: Env): Env = Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst, exprCode ++ that.exprCode, bound ++ that.bound)

    // TODO: Voir ou est-ce que ce truc est utilisé
    override def expand(expr: Expr): Expr = expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }

    // TODO: Peut-on supposer que expr a été simplifié??? Il semblerait que non!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    override def implies(expr: Expr): Boolean = {
       if (expr.getType != BooleanType()) false
       else {
         given Subst = mkSubst
         // TODO: Purity????
         ocbsl.implied(ocbsl.codeOf(expr))
       }
    }

    def mkSubst: Subst = {
      // TODO: Ok?
      Subst(conditions, free = exprCode, bound = Map.empty, 0, letDef = Map.empty)
        .withOpenBounds(bound)
    }
  }

  object Env extends PathProvider[Env] {
    def empty: Env = Env(Set.empty, Map.empty, Map.empty, Seq.empty)
  }

  override def initEnv: Env = Env.empty

  enum LabelledPattern {
    case Wildcard
    case ADT(id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern])
    case TuplePattern(sub: Seq[LabelledPattern])
    case Lit[T](lit: Literal[T])
    // TODO: What is recs???
    case Unapply(recs: Seq[Code], id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern])
  }

  case class LabMatchCase(pattern: LabelledPattern, guard: Code, rhs: Code)

  enum Label {
    case Var(v: Variable)
    case IndexedVar(i: Int)
    case Let // Indexed
    case Tuple
    case ADT(id: Identifier, tps: Seq[Type])
    // TODO: Trimbaler ce ctor n'est pas très joli non?
    case ADTSelector(adt: ADTType, ctor: TypedADTConstructor, selector: Identifier)
    case FunctionInvocation(id: Identifier, tps: Seq[Type])
    case Annotated(flags: Seq[Flag])
    case IsConstructor(adt: ADTType, id: Identifier)
    case Assume
    case Assert
    case Require
    case Ensuring
    case MatchExpr(patterns: Seq[LabelledPattern])
    case IfExpr
    case Application
    case Lambda(nbParams: Int) // Indexed
    case Choose // Indexed
    case Forall(nbParams: Int) // Indexed

    case Or
    case Not

    case Equals
    case LessThan
    case GreaterThan
    case LessEquals
    case GreaterEquals

    case UMinus
    case Plus
    case Minus
    case Times
    case Division
    case Remainder
    case Modulo

    case BVNot
    case BVAnd
    case BVOr
    case BVXor
    case BVShiftLeft
    case BVAShiftRight
    case BVLShiftRight

    case BVNarrowingCast(newType: BVType)
    case BVWideningCast(newType: BVType)
    case BVUnsignedToSigned
    case BVSignedToUnsigned

    case Lit[T](lit: Literal[T])

    case TupleSelect(index: Int)

    case FiniteSet(base: Type)
    // TODO: SetOps

    // TODO: Bag, etc.

    case FiniteArray(base: Type)
    // TODO: Comme args, il y a elems.values ++ Seq(default, size)
    //  On utilise indices pour reconstruire elems
    case LargeArray(elemsIndices: Seq[Int], base: Type)
    case ArraySelect
    case ArrayUpdated
    case ArrayLength
  }

  // TODO: Si on fait un summon[Ordering[Int]] dans OCBSL, ça loop...
  private val intOrdering = summon[Ordering[Int]]

  // TODO: On pourrait simplifier les trucs du genre !isInstanceOf[A] && isInstanceOf[B] en isInstanceOf[B] pour les patmat?
  object OCBSL {
    // `Code` wrapped here to avoid accidental conversion from Int to Code
    opaque type Code = Int

    object Code {
      def fromInt(i: Int): Code = i
    }

    given Ordering[Code] = intOrdering

    case class Signature(label: Label, children: Seq[Code])

    // TODO: Rename
    case class Subst(conditions: Set[Code],
                     free: Map[Variable, Code],
                     bound: Map[Variable, Int],
                     nestingLevel: Int,
                     // variable -> code de la *definition* pas de le code de l'indexed var
                     // et si on peut utiliser ce code là au lieu de l'indexed var.
                     // "true" en général, sauf pour les lambdas dans la var apparait plsrs fois.
                     // Le "uncodeOf" se débrouillera pour faire la substitution inverse, du code de la def à la var
                     letDef: Map[Variable, (Code, Boolean)]) {
      def withCond(c: Code): Subst = copy(conditions = conditions + c)
      def withConds(cs: Set[Code]): Subst = copy(conditions = conditions ++ cs)

      def withLetBound(vd: ValDef, c: Code, canSubst: Boolean): Subst =
        withLetBounds(Seq((vd, c)), canSubst)
//        Subst(conditions, free, bound + (vd.toVariable -> nestingLevel), nestingLevel + 1, letDef + (vd.toVariable -> (c, canSubst)))

      def withLetBounds(vds: Seq[(ValDef, Code)], canSubst: Boolean): Subst = {
        // Note: params may be empty, which is fine (the nesting level will not increase)

        assert(letDef.values.map(_._1).toSet.intersect(vds.map(_._2).toSet).isEmpty)
        assert(letDef.keySet.intersect(vds.map(_._1.toVariable).toSet).isEmpty)

        Subst(conditions, free,
          bound ++ vds.zipWithIndex.map { case ((vd, _), i) => vd.toVariable -> (nestingLevel + i) }.toMap,
          nestingLevel + vds.size,
          letDef ++ vds.map((vd, c) => vd.toVariable -> (c, canSubst)))
      }

      def withOpenBound(param: ValDef): Subst = withOpenBounds(Seq(param))

      def withOpenBounds(params: Seq[ValDef]): Subst = {
        // Note: params may be empty, which is fine (the nesting level will not increase)
        Subst(conditions, free,
          bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> (nestingLevel + i)).toMap,
          nestingLevel + params.size, letDef)
      }

      // TODO: Sert à rien, puisque c'est pop...
      lazy val revLetDef: Map[Code, Variable] = letDef.map { case (v, (c, _)) => c -> v }
    }

    enum Purity {
      case Pure
      case Impure
      case Delayed(blockers: Set[Identifier])

      def ++(that: => Purity): Purity = {
        if (this == Impure) Impure
        else (this, that) match { // TODO: Evaluated once or multiple time?
          case (Pure, Pure) => Pure
          case (Delayed(s1), Delayed(s2)) => Delayed(s1 ++ s2)
          case (Delayed(s1), Pure) => Delayed(s1)
          case (Pure, Delayed(s2)) => Delayed(s2)
          case _ => Impure
        }
      }

      def isPure: Boolean = this match {
        case Pure => true
        case _ => false
      }
    }

    object Purity {
      def fold(xs: Seq[Purity]): Purity = xs.foldLeft(Pure)(_ ++ _)
      def fromBoolean(isPure: Boolean): Purity = if (isPure) Pure else Impure
    }

  }

  // TODO (liste de rappel):
  //    - Pour le "uncodeOf", pour éviter des duplication, on pourra let-bind les codes pour lesquelles
  //    les expr. sont non triviales
  //    - Pourrait-on envisager de supprimer les indexed var pour les lets (slmt pour les lets) et simplement utiliser les codes
  //    des definitions? On maintiendra un Let(def, body) et le "uncodeOf" pourra l'utiliser pour savoir
  //    où remettre le let (et là, on pourra même le supprimer si def est pas utilisé et qu'il est pur)
  //    Cela nous permettra d'éviter de devoir faire des substitutions explicites
  //      - Attention au gag avec les lambdas!! On risquera de tout inliner dans le truc de simplification...
  //        Sauf si: On arrive a flairer le truc et qu'on arrive a voir combien il y a de references a cette lambda
  //        si cest let-bound etc.
  class OCBSL {
    import scala.collection.mutable
    import Purity._

    // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

    private val sig2code = mutable.Map.empty[Signature, Code]
    private val code2sig = mutable.Map.empty[Code, Signature]
    private val sizeCache = mutable.Map.empty[Expr, Int]
    private val codeTpe = mutable.Map.empty[Code, Type]

    private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
    private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
    private val falseCode = updateCodesSig(falseSig, Pure, BooleanType())
    private val trueCode = updateCodesSig(trueSig, Pure, BooleanType())

    private val purityCache = mutable.Map.empty[Identifier, Boolean]
    private val codePurityCache = mutable.Map.empty[Code, Boolean]
    private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
    private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
    private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V
    private val visiting = mutable.Set.empty[Identifier]

    def codePurity(c: Code): Purity = {
      assert(code2sig.contains(c))
      codePurityCache.get(c)
        .map(fromBoolean)
        .getOrElse(Delayed(codeBlockedBy(c)))
    }

    def codeOf(e: Expr)(using subst: Subst): Code = simplifiedDisjunction(pDisj(e).toSet)

    def negCodeOf(c: Code)(using Subst): Code = updateCodesSig(pNegNormal(c), codePurity(c), BooleanType())

    def fnPurity(fn: Identifier)(using subst: Subst): Purity = {
      def resolvedPurity(isPure: Boolean): Unit = {
        if (blocking.contains(fn)) {
          val (blockedFns, blockedCodes) = blocking.remove(fn).get
          purityCache += fn -> isPure
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

      purityCache.get(fn) match {
        case Some(true) => Pure
        case Some(false) => Impure
        case None =>
          // TODO: Quid condition venant du simplifier (s'il y en as???)?
          // TODO: Différencier:
          //    -outer assms et local assms
          //    -outer open bound et local open bound
          given Subst = Subst(Set.empty, subst.free, Map.empty, 0, Map.empty)
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val res = codePurity(codeOf(getFunction(fn).fullBody))
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

    // TODO: Pk ce truc est fait dans codeOf mais pas dans pDisj?
    def simplifiedDisjunction(disj: Set[Code]): Code = {
      // TODO: Caching?
      val purity = fold(disj.map(codePurity).toSeq)
      val disj1 = disj.filter(_ != falseCode)
      if (disj1.isEmpty) falseCode
      else if (disj1.size == 1) disj1.head
      else if (purity.isPure && (disj1.contains(trueCode) || checkForContradiction(disj1))) trueCode
      else {
        val sig = Signature(Label.Or, disj1.toSeq.sorted)
        updateCodesSig(sig, purity, BooleanType())
      }
    }

    // Is `c` an ADT with constructor `id`?
    //   Some(true) - Yes
    //   Some(false) - No
    //   None - Can't tell
    def isConstructor(c: Code, adt: ADTType, id: Identifier)(using subst: Subst): Option[Boolean] = {
      // TODO: What about purity?
      def codeIsCtor(ofId: Identifier): Code =
        updateCodesSig(Signature(Label.IsConstructor(adt, ofId), Seq(c)), codePurity(c), BooleanType())
      def codeNotCtor(ofId: Identifier): Code =
        negCodeOf(codeIsCtor(ofId))

      code2sig(c) match {
        case Signature(Label.ADT(id2, _), _) => Some(id == id2)
        case _ =>
          if (implied(codeIsCtor(id))) Some(true)
          else if (implied(codeNotCtor(id))) Some(false)
          else {
            val sort = adt.getSort
            val cons = getConstructor(id, adt.tps)
            // All other constructors (excluding `id`) for the ADT
            val alts = (sort.constructors.toSet - cons).map(_.id)

            if (alts.exists(alt => implied(codeIsCtor(alt)))) Some(false)
            else if (alts.forall(alt => implied(codeNotCtor(alt)))) Some(true)
            else None
          }
      }
    }

    def sigOfIndexedVar(lvl: Int)(using subst: Subst): Signature = {
      assert(lvl < subst.nestingLevel)
      mkIxVar(subst.nestingLevel - lvl)
    }

    def codeOfIndexedVar(lvl: Int, tpe: Type)(using subst: Subst): Code = updateCodesSig(sigOfIndexedVar(lvl), Pure, tpe)

    def sigOfVariable(v: Variable)(using subst: Subst): Signature = {
      subst.free.get(v).map(code2sig) // Check if `v` is a "free" variable (free w.r.t. OCBSL, but bound w.r.t. Env)
        // Check if `v` is let-bound *and* that we can use the signature/code of the definition of v
        .orElse(subst.letDef.get(v).filter(_._2).map((c, _) => code2sig(c)))
        // Check if `v` is bound to a lambda, choose forall or let (for which the substitution was forbidden)
        .orElse(subst.bound.get(v).map(sigOfIndexedVar))
        .getOrElse(mkFreeVar(v))
    }

    def codeOfVariable(v: Variable)(using Subst): Code = updateCodesSig(sigOfVariable(v), Pure, v.getType)

    def mkFreeVar(v: Variable): Signature = Signature(Label.Var(v), Seq.empty)
    def mkIxVar(i: Int): Signature = Signature(Label.IndexedVar(i), Seq.empty)
    def mkLet(e: Code, body: Code): Signature = Signature(Label.Let, Seq(e, body))
    def mkTuple(args: Seq[Code]): Signature = {
      assert(args.size >= 2)
      Signature(Label.Tuple, args)
    }
    def mkADT(id: Identifier, tps: Seq[Type], args: Seq[Code]): Signature = Signature(Label.ADT(id, tps), args)
    def mkADTSelector(recv: Code, adt: ADTType, ctor: TypedADTConstructor, selector: Identifier): Signature = Signature(Label.ADTSelector(adt, ctor, selector), Seq(recv))
    def mkFunInvoc(id: Identifier, tps: Seq[Type], args: Seq[Code]): Signature = Signature(Label.FunctionInvocation(id, tps), args)
    def mkAnnot(e: Code, flags: Seq[Flag]): Signature = Signature(Label.Annotated(flags), Seq(e))
    def mkIsCtor(e: Code, adt: ADTType, id: Identifier): Signature = Signature(Label.IsConstructor(adt, id), Seq(e))
    def mkAssume(pred: Code, body: Code): Signature = Signature(Label.Assume, Seq(pred, body))
    def mkAssert(pred: Code, body: Code): Signature = Signature(Label.Assert, Seq(pred, body))
    def mkRequire(pred: Code, body: Code): Signature = Signature(Label.Require, Seq(pred, body))
    def mkEnsuring(body: Code, pred: Code): Signature = Signature(Label.Ensuring, Seq(body, pred))
    def mkMatchExpr(scrut: Code, cases: Seq[LabMatchCase]): Signature = {
      assert(cases.nonEmpty)
      val (pats, guards, rhs) = cases.map(mc => (mc.pattern, mc.guard, mc.rhs)).unzip3
      Signature(Label.MatchExpr(pats), scrut +: guards.zip(rhs).flatMap((g, r) => Seq(g, r)))
    }
    def mkIfExpr(cond: Code, thn: Code, els: Code): Signature = Signature(Label.IfExpr, Seq(cond, thn, els))
    def mkApp(callee: Code, args: Seq[Code]): Signature = Signature(Label.Application, callee +: args)
    def mkLambda(nbParams: Int, body: Code): Signature = Signature(Label.Lambda(nbParams), Seq(body))
    def mkWickedChoose(pred: Code): Signature = Signature(Label.Choose, Seq(pred))
    def mkForall(nbParams: Int, pred: Code): Signature = Signature(Label.Forall(nbParams), Seq(pred))
    def mkOr(es: Seq[Code]): Signature = Signature(Label.Or, es.sorted.distinct)
    def mkNot(e: Code): Signature = Signature(Label.Not, Seq(e))
    def mkEquals(e1: Code, e2: Code): Signature = Signature(Label.Equals, Seq(e1, e2).sorted)
    def mkLessThan(e1: Code, e2: Code): Signature = Signature(Label.LessThan, Seq(e1, e2))
    def mkGreaterThan(e1: Code, e2: Code): Signature = Signature(Label.GreaterThan, Seq(e1, e2))
    def mkLessEquals(e1: Code, e2: Code): Signature = Signature(Label.LessEquals, Seq(e1, e2))
    def mkGreaterEquals(e1: Code, e2: Code): Signature = Signature(Label.GreaterEquals, Seq(e1, e2))
    def mkUMinus(e: Code): Signature = Signature(Label.UMinus, Seq(e))
    def mkPlus(e1: Code, e2: Code): Signature = Signature(Label.Plus, Seq(e1, e2).sorted)
    def mkMinus(e1: Code, e2: Code): Signature = Signature(Label.Minus, Seq(e1, e2))
    def mkTimes(e1: Code, e2: Code): Signature = Signature(Label.Times, Seq(e1, e2).sorted)
    def mkDivision(e1: Code, e2: Code): Signature = Signature(Label.Division, Seq(e1, e2))
    def mkRemainder(e1: Code, e2: Code): Signature = Signature(Label.Remainder, Seq(e1, e2))
    def mkModulo(e1: Code, e2: Code): Signature = Signature(Label.Modulo, Seq(e1, e2))
    def mkBVNot(e: Code): Signature = Signature(Label.BVNot, Seq(e))
    def mkBVAnd(e1: Code, e2: Code): Signature = Signature(Label.BVAnd, Seq(e1, e2).sorted)
    def mkBVOr(e1: Code, e2: Code): Signature = Signature(Label.BVOr, Seq(e1, e2).sorted)
    def mkBVXor(e1: Code, e2: Code): Signature = Signature(Label.BVXor, Seq(e1, e2).sorted)
    def mkBVShiftLeft(e1: Code, e2: Code): Signature = Signature(Label.BVShiftLeft, Seq(e1, e2))
    def mkBVAShiftRight(e1: Code, e2: Code): Signature = Signature(Label.BVAShiftRight, Seq(e1, e2))
    def mkBVLShiftRight(e1: Code, e2: Code): Signature = Signature(Label.BVLShiftRight, Seq(e1, e2))
    def mkBVNarrowingCast(e: Code, newType: BVType): Signature = Signature(Label.BVNarrowingCast(newType), Seq(e))
    def mkBVWideningCast(e: Code, newType: BVType): Signature = Signature(Label.BVWideningCast(newType), Seq(e))
    def mkBVUnsignedToSigned(e: Code): Signature = Signature(Label.BVUnsignedToSigned, Seq(e))
    def mkBVSignedToUnsigned(e: Code): Signature = Signature(Label.BVSignedToUnsigned, Seq(e))
    def mkLit[T](l: Literal[T]): Signature = Signature(Label.Lit(l), Seq.empty)
    def mkTupleSelect(recv: Code, i: Int): Signature = Signature(Label.TupleSelect(i), Seq(recv))
    def mkFiniteSet(elems: Seq[Code], base: Type): Signature = Signature(Label.FiniteSet(base), elems)
    def mkFiniteArray(elems: Seq[Code], base: Type): Signature = Signature(Label.FiniteArray(base), elems)
    def mkLargeArray(elems: Map[Int, Code], default: Code, size: Code, base: Type): Signature = {
      val (elemsIndices, elemsCodes) = elems.toSeq.sortBy(_._1).unzip
      Signature(Label.LargeArray(elemsIndices, base), elemsCodes ++ Seq(default, size))
    }
    def mkArraySelect(arr: Code, i: Code): Signature = Signature(Label.ArraySelect, Seq(arr, i))
    def mkArrayUpdated(arr: Code, i: Code, v: Code): Signature = Signature(Label.ArrayUpdated, Seq(arr, i, v))
    def mkArrayLength(arr: Code): Signature = Signature(Label.ArrayLength, Seq(arr))

    def computeSignature(e: Expr)(using subst: Subst): (Signature, Purity) = {
//      codes.get(e).map(c => (code2sig(c), codePurity(c))) match {
//        case Some((sig, purity)) => return (sig, purity)
//        case None => ()
//      }

      val tpe = e.getType
      val (sig, purity) = e match {
        case v: Variable =>
          (sigOfVariable(v), Pure) // TODO

        case Assume(pred, body) =>
          val cPred = codeOf(pred)
          val cBody = codeOf(body)(using subst.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
          simplifySigTopLvl(mkAssume(cPred, cBody), tpe)

        case Assert(pred, _, body) =>
          val cPred = codeOf(pred)
          val cBody = codeOf(body)(using subst.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
          simplifySigTopLvl(mkAssert(cPred, cBody), tpe)

        case Require(pred, body) =>
          val cPred = codeOf(pred)
          val cBody = codeOf(body)(using subst.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
          simplifySigTopLvl(mkRequire(cPred, cBody), tpe)

        case Ensuring(body, pred) =>
          val cBody = codeOf(body)
          val cPred = codeOf(pred)
          simplifySigTopLvl(mkEnsuring(cBody, cPred), tpe)

        case Tuple(args) =>
          simplifySigTopLvl(mkTuple(args.map(codeOf)), tpe)

        case ADT(id, tps, args) =>
          simplifySigTopLvl(mkADT(id, tps, args.map(codeOf)), tpe)

        case MatchExpr(scrut, cases) =>
          def processPattern(subScrut: Code, scrutTpe: Type, pat: Pattern): (LabelledPattern, Seq[(ValDef, Code)], Set[Code]) = {
            // On doit être vigilent avec les subst implicites qu'on utilise!!!
            given dontDefaultUseOuterSubst: Subst = sys.error("Carefully consider the appropriate subst to use")
            val pSubScrut = codePurity(subScrut)
            val vdBinder: ValDef = pat.binder.getOrElse(ValDef.fresh("dummyBinder", scrutTpe))
            val bdgs1 = Seq((vdBinder, subScrut))
            pat match {
              case WildcardPattern(_) => (LabelledPattern.Wildcard, bdgs1, Set.empty)
              case ADTPattern(_, id, tps, subps) =>
                val adt = ADTType(id, tps)
                val tcons = getConstructor(id, tps)
                assert(tcons.fields.size == subps.size)
                val conds1 = updateCodesSig(mkIsCtor(subScrut, adt, id), pSubScrut, BooleanType())
                val (labSubPats, bdgs2, conds2) = tcons.fields.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, Set(conds1))) {
                  // TODO: Annoté en dropvc?
                  case ((labSubPatAcc, bdgsAcc, condsAcc), (fld, subpat)) =>
                    // TODO: Il nous faut un adt selector
                    // TODO: Ok????
                    // TODO: Purity de toussa??? devrait on inclure purity scrut???
                    val newScrut = updateCodesSig(mkADTSelector(subScrut, adt, tcons, fld.id), pSubScrut, fld.getType)
                    val (labSubPat, newBdgs, newConds) = processPattern(newScrut, fld.getType, subpat)
                    (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
                }
                (LabelledPattern.ADT(id, tps, labSubPats), bdgs2, conds2)
              case LiteralPattern(_, lit) => (LabelledPattern.Lit(lit), bdgs1, Set.empty)
              case UnapplyPattern(_, recs, id, tps, subps) =>
                // TODO: !!!! Si on utilise codeOf, ne pas oublier d'utiliser le subst approprié !!!
                sys.error(s"Does not know how to handle $pat")
            }
          }

          val cScrut = codeOf(scrut)
          val pScrut = codePurity(cScrut)

          // accumulatedConds: la negation des conds des cases antérieures
          def processCase(mc: MatchCase, accumulatedConds: Set[Code]): Option[(LabMatchCase, Set[Code], Boolean)] = {
            given dontDefaultUseOuterSubst: Subst = sys.error("Carefully consider the appropriate subst to use")
            // patConds: SANS le guard!!!
            val (labPat, bdgs, patConds) = processPattern(cScrut, scrut.getType, mc.pattern)
            // TODO: canSubst?
            val subst1 = subst.withLetBounds(bdgs, canSubst = true).withConds(accumulatedConds ++ patConds)
            val cGuard = mc.optGuard.map(codeOf(_)(using subst1)).getOrElse(trueCode)
            val subst2 = subst1.withCond(cGuard)

            val cRhs = codeOf(mc.rhs)(using subst2)
//            // TODO: Non non non, les bdgs ne seront pas "visible" pour les guard???
//            val cRhs1 = letBind(bdgs.map(_._2))(cRhs0, mc.rhs.getType)

            if (pScrut.isPure) {
              // TODO: Ok par rapport à la pureté?

              if (implied(trueCode)(using subst2)) {
                // TODO: A-t-on besoin de faire qqchose pour ces bindings?
//                val subst3: Subst = ???
//                val cRhs = codeOf(mc.rhs)(using subst2)
                return Some(LabMatchCase(LabelledPattern.Wildcard, trueCode, cRhs), Set(trueCode), true)
              } else if (implied(falseCode)(using subst2)) {
                // Unreachable
                return None
              }
            }
//            val cRhs = codeOf(mc.rhs)(using subst2)
            Some(LabMatchCase(labPat, cGuard, cRhs), patConds + cGuard, false)
          }

          def processCases(cases: Seq[MatchCase], accumulatedConds: Set[Code], acc: Seq[LabMatchCase]): (Seq[LabMatchCase], Boolean) = {
            given dontDefaultUseOuterSubst: Subst = sys.error("Carefully consider the appropriate subst to use")
            if (cases.isEmpty) (acc, false)
            else {
              processCase(cases.head, accumulatedConds) match {
                case Some((labMatchCase, caseConds, allCovered)) =>
                  if (allCovered) (acc :+ labMatchCase, true)
                  else {
                    val negCaseConds = negatedConjunction(caseConds)(using subst)
                    processCases(cases.tail, accumulatedConds + negCaseConds, acc :+ labMatchCase)
                  }
                case None =>
                  processCases(cases.tail, accumulatedConds, acc)
              }
            }
          }

          // TODO: Quid pureté???? Et celle des guard+rhs????
          processCases(cases, Set.empty, Seq.empty) match {
            // TODO: Et simplifySigTopLvl ???
            case (Seq(), _) =>
              ???
            case (Seq(matchCase), true) =>
              // Remarque: si allCovered = true, alors on a forcément un wildcard pattern (et aucune subst n'est nécessaire)
              assert(matchCase.pattern == LabelledPattern.Wildcard)
              // TODO: Et simplifySigTopLvl ???
              // TODO: Autre chose pour les bdgs?
              (code2sig(matchCase.rhs), pScrut)
            case (matchCases, _) =>
              // TODO: Et simplifySigTopLvl ???
              (mkMatchExpr(cScrut, matchCases), pScrut)
          }

        case s @ ADTSelector(e, selector) =>
          val adt @ ADTType(_, _) = e.getType
          simplifySigTopLvl(mkADTSelector(codeOf(e), adt, s.constructor, selector), tpe)

        case FunctionInvocation(id, tps, args) =>
          val cs = args.map(codeOf)
          lazy val callPurity = {
            if (visiting.contains(id)) {
              if (!opts.assumeChecked) Impure
              else Delayed(Set(id))
            }
            else fnPurity(id)
          }
          // TODO: Pk ne pousse-t-on pas cela dans simplifyTopLvlSig??
          val purity = fold(cs.map(codePurity)) ++ callPurity
          (mkFunInvoc(id, tps, cs), purity) // TODO

        case Application(callee, args) =>
          simplifySigTopLvl(mkApp(codeOf(callee), args.map(codeOf)), tpe)

        // TODO: Pour les cas ou on a besoin d'une réponse "tout de suite" pour procéder à des simplification, comment s'y prendre???
        case IfExpr(cond, thenn, elze) =>
          val cCond = codeOf(cond)
          // TODO: Si on ajoute false, est-ce que ça joue qd meme?
          val cThen = codeOf(thenn)(using subst.withCond(cCond))
          val cElse = codeOf(elze)(using subst.withCond(negCodeOf(cCond)))
          simplifySigTopLvl(mkIfExpr(cCond, cThen, cElse), tpe)

        case IsConstructor(e, id) =>
          val adt @ ADTType(_, _) = e.getType
          simplifySigTopLvl(mkIsCtor(codeOf(e), adt, id), tpe)

        case Let(vd, e, body) =>
          val cE = codeOf(e)
          // TODO: Ok par rapport à la pureté et ces subst?
          val canSubst = code2sig(cE) match {
            case Signature(Label.Lambda(_), _) =>
              val v = vd.toVariable
              // TODO: Par rapport à orig body, et pas simplified body --'
              // TODO: !!!! ??? immediateCall + inLambda ??? !!!!
              //    pour le "immediateCall": ? p-e par rapport au path condition supplémentaire résultant de stmts intermediaire avant le call?
              //    pour le "inLambda": pour eviter explosion en cas d'inling lambda (~> à gérer dans "uncodeOf"?)
              exprOps.count { case `v` => 1 case _ => 0 } (body) <= 1
            case _ => true
          }
          val cB = codeOf(body)(using subst.withLetBound(vd, cE, canSubst))
          simplifySigTopLvl(mkLet(cE, cB), tpe)

        case Lambda(params, body) =>
          val c = codeOf(body)(using subst.withOpenBounds(params))
          simplifySigTopLvl(mkLambda(params.size, c), tpe)

        case Choose(res, pred) =>
          val c = codeOf(pred)(using subst.withOpenBound(res))
          simplifySigTopLvl(mkWickedChoose(c), tpe)

        case Forall(params, body) =>
          val c = codeOf(body)(using subst.withOpenBounds(params))
          simplifySigTopLvl(mkForall(params.size, c), tpe)

        // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
        // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
        //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
        //  une map ad-hoc qui contient ces infos...?
        case Annotated(e, flags) =>
          // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
          //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
          //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
          simplifySigTopLvl(mkAnnot(codeOf(e), flags), tpe)

        // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
        case and @ And(_) =>
          val ands = unAnd(and)
          val c = codeOf(Not(Or(ands.map(Not.apply))))
          (code2sig(c), codePurity(c))
        case or @ Or(_) =>
          // TODO: checkForContradiction?
          // TODO: Pas d'incohérence avec purity? (p.ex. un code qui est pure, mais pas l'autre)?
          val cs = unOr(or).map(codeOf).sorted.distinct
          // TODO: Move simplifyTopLvlSig
          (mkOr(cs), fold(cs.map(codePurity)))
        case Not(e) => pNeg(e) // TODO: ? pk pas simplifyTopLvlSig?
        case Implies(e1, e2) =>
          val c = codeOf(Or(Not(e1), e2))
          (code2sig(c), codePurity(c))
        case Equals(e1, e2) =>
          simplifySigTopLvl(mkEquals(codeOf(e1), codeOf(e2)), tpe)
        case LessThan(e1, e2) =>
          simplifySigTopLvl(mkLessThan(codeOf(e1), codeOf(e2)), tpe)
        case GreaterThan(e1, e2) =>
          simplifySigTopLvl(mkGreaterThan(codeOf(e1), codeOf(e2)), tpe)
        case LessEquals(e1, e2) =>
          simplifySigTopLvl(mkLessEquals(codeOf(e1), codeOf(e2)), tpe)
        case GreaterEquals(e1, e2) =>
          simplifySigTopLvl(mkGreaterEquals(codeOf(e1), codeOf(e2)), tpe)
        case UMinus(e) =>
          simplifySigTopLvl(mkUMinus(codeOf(e)), tpe)

        case Plus(e1, e2) =>
          simplifySigTopLvl(mkPlus(codeOf(e1), codeOf(e2)), tpe)
        case Minus(e1, e2) =>
          simplifySigTopLvl(mkMinus(codeOf(e1), codeOf(e2)), tpe)
        case Times(e1, e2) =>
          simplifySigTopLvl(mkTimes(codeOf(e1), codeOf(e2)), tpe)
        case Division(e1, e2) =>
          simplifySigTopLvl(mkDivision(codeOf(e1), codeOf(e2)), tpe)
        case Remainder(e1, e2) =>
          simplifySigTopLvl(mkRemainder(codeOf(e1), codeOf(e2)), tpe)
        case Modulo(e1, e2) =>
          simplifySigTopLvl(mkModulo(codeOf(e1), codeOf(e2)), tpe)

        case BVNot(e) =>
          simplifySigTopLvl(mkBVNot(codeOf(e)), tpe)
        case BVAnd(e1, e2) =>
          simplifySigTopLvl(mkBVAnd(codeOf(e1), codeOf(e2)), tpe)
        case BVOr(e1, e2) =>
          simplifySigTopLvl(mkBVOr(codeOf(e1), codeOf(e2)), tpe)
        case BVXor(e1, e2) =>
          simplifySigTopLvl(mkBVXor(codeOf(e1), codeOf(e2)), tpe)
        case BVShiftLeft(e1, e2) =>
          simplifySigTopLvl(mkBVShiftLeft(codeOf(e1), codeOf(e2)), tpe)
        case BVAShiftRight(e1, e2) =>
          simplifySigTopLvl(mkBVAShiftRight(codeOf(e1), codeOf(e2)), tpe)
        case BVLShiftRight(e1, e2) =>
          simplifySigTopLvl(mkBVLShiftRight(codeOf(e1), codeOf(e2)), tpe)

        case BVNarrowingCast(e, newType) =>
          simplifySigTopLvl(mkBVNarrowingCast(codeOf(e), newType), tpe)
        case BVWideningCast(e, newType) =>
          simplifySigTopLvl(mkBVWideningCast(codeOf(e), newType), tpe)
        case BVUnsignedToSigned(e) =>
          simplifySigTopLvl(mkBVUnsignedToSigned(codeOf(e)), tpe)
        case BVSignedToUnsigned(e) =>
          simplifySigTopLvl(mkBVUnsignedToSigned(codeOf(e)), tpe)

        case TupleSelect(e, index) =>
          simplifySigTopLvl(mkTupleSelect(codeOf(e), index), tpe)

        case FiniteArray(elems, base) =>
          simplifySigTopLvl(mkFiniteArray(elems.map(codeOf), base), tpe)
        case LargeArray(elems, default, size, base) =>
          simplifySigTopLvl(mkLargeArray(elems.map((i, e) => i -> codeOf(e)), codeOf(default), codeOf(size), base), tpe)
        case ArraySelect(array, index) =>
          simplifySigTopLvl(mkArraySelect(codeOf(array), codeOf(index)), tpe)
        case ArrayUpdated(array, index, value) =>
          simplifySigTopLvl(mkArrayUpdated(codeOf(array), codeOf(index), codeOf(value)), tpe)
        case ArrayLength(array) =>
          simplifySigTopLvl(mkArrayLength(codeOf(array)), tpe)

        case l: Literal[_] =>
          (mkLit(l), Pure)

        case e =>
          println("Do not know how to handle "+e)
          ???
//          // println(s"Generated an 'unknown' for $e (with id $unknownCounter)")
//          val sig = Signature(Label.Unknown(unknownCounter), Seq.empty)
//          unknownCounter += 1
//          // TODO: Impure car risque de supprimer qqchose qui peut etre utile? (malgré opts.assumeChecked)
//          (sig, Impure)
      }

      val code = updateCodesSig(sig, purity, tpe)
      val simpSig = {
        if (purity.isPure && tpe == BooleanType() && implied(code)) trueSig
        else sig
      }
      (simpSig, purity)
    }

    def implied(rhs: Code)(using subst: Subst): Boolean = {
      if (subst.conditions.isEmpty) rhs == trueCode
      else {
        // TODO: Quid purité de rhs???
        // TODO: Pourrait-on envisager de cache subst.condition?
        // TODO: Un subst comme ça ne permettra pas de bénéficier d'eventuelles simplifications!!!!
        // a ==> b === a && b = a
        val lhsConj = conjunct(subst.conditions)
        val rhsLhsConj = conjunct(Set(lhsConj, rhs))
        rhsLhsConj == lhsConj
      }
    }

    def conjunct(conj: Set[Code])(using Subst): Code = negCodeOf(negatedConjunction(conj))

    def negatedConjunction(conj: Set[Code])(using Subst): Code= {
      // TODO: Caching?
      simplifiedDisjunction(conj.map(negCodeOf))
    }

    def checkForContradiction(disj: Set[Code]): Boolean = {
      if (disj.exists(c => !codePurity(c).isPure)) {
        return false
      }

      // TODO: Relativement different par rapport à l'orig
      val (pos, neg) = disj.foldLeft((Set.empty[Code], Set.empty[Code])) {
        case ((posAcc, negAcc), c) =>
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

    // TODO: Cela suppose que c'est une disjunction, mais c'est p-e pas le cas??? Ca peut etre une expr d'un autre type!!!
    // TODO: Ok?
    // TODO: Cache?
    def pDisj(e: Expr)(using Subst): Seq[Code] = {
      assert(e.getType == BooleanType())
      computeSignature(e) match {
        case (Signature(Label.Or, children), _) => children
        case (sig, p) => Seq(updateCodesSig(sig, p, BooleanType()))
      }
    }

    // Signature de Not(child)
    def pNeg(child: Expr)(using Subst): (Signature, Purity) = {
//      codes.get(child) match {
//        case Some(c) => return (pNegNormal(c), codePurity(c))
//        case None => ()
//      }

      // TODO: Où devrait-on mettre le caching? C'est appelé par computeSignature donc ça devrait faire l'affaire non?

      child match {
        case Not(e) => computeSignature(e) // TODO: Orig fait pDisj, mais pDisj et un computeSignature pour nous (du moins, pour le moment)
        case or @ Or(_) =>
          // Note: ors cannot be empty (by Or `require`)
          val ors0 = unOr(or)
          val ors1 = ors0.sortBy(sizeOf)
          // TODO: Ici, on fait un filter..distinct.sorted, ce que l'orig ne fait pas vraiment?
          val r = ors1.tail.flatMap(pDisj)
            .filter(_ != falseCode)
            .sorted.distinct
          if (r.isEmpty) pNeg(ors1.head) // TODO: Caching?
          else {
            // TODO: Ok?
            // TODO: Ressemble pas mal à simplifiedDisjunction
            val s = (pDisj(ors1.head) ++ r)
              .filter(_ != falseCode)
              .sorted.distinct
            val purity = fold(s.map(codePurity))
            if (purity.isPure && (s.contains(trueCode) || checkForContradiction(s.toSet))) (falseSig, Pure)
            else if (s.size == 1) (pNegNormal(s.head), purity)
            else {
              val orCode = updateCodesSig(Signature(Label.Or, s), purity, BooleanType())
              (Signature(Label.Not, Seq(orCode)), purity)
            }
          }
        case _ =>
          // TODO: Ok?
          computeSignature(child) match {
            case (Signature(Label.Lit(BooleanLiteral(b)), Seq()), Pure) =>
              (Signature(Label.Lit(BooleanLiteral(!b)), Seq.empty), Pure)
            case (sig, purity) =>
              // TODO: Ok?
              (Signature(Label.Not, Seq(sig2code(sig))), purity)
          }
      }
    }

    // TODO: ok?
    // TODO: caching?
    // TODO: En gros la signature de Not(c)
    def pNegNormal(c: Code): Signature = {
      assert(code2sig.contains(c))
      code2sig(c) match {
        case Signature(Label.Not, Seq(cc)) => code2sig(cc)
        case Signature(_, _) => Signature(Label.Not, Seq(c)) // TODO: Ok?
      }
    }

    def codeOfIntLit(lit: BigInt, tpe: Type)(using Subst): Code = codeOf(intLitOfType(lit, tpe))

    def intLitOfType(lit: BigInt, tpe: Type): Expr = tpe match {
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

    def updateCodesSig(sig: Signature, purity: Purity, tpe: Type): Code = {
      sig2code.get(sig) match {
        case Some(c) =>
          // TODO: Quid purity et type coherence????
          c
        case None =>
          val newCode = Code.fromInt(sig2code.size)
          assert(!code2sig.contains(newCode))
          sig2code += sig -> newCode
          code2sig += newCode -> sig
          codeTpe += newCode -> tpe
          purity match {
            case Pure => codePurityCache += newCode -> true
            case Impure => codePurityCache += newCode -> false
            case Delayed(blockers) =>
              codeBlockedBy += newCode -> blockers
              for (blocker <- blockers) {
                val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
                blocking += blocker -> (blockedFns, blockedCodes + newCode)
              }
          }
          newCode
      }
    }

    def letBind(bdgs: Seq[Code]): (Code, Type) => Code = { (body, tpe) =>
      bdgs.foldRight(body) {
        case (let, rest) =>
          // TODO: purity ok?
          updateCodesSig(mkLet(let, body), codePurity(let) ++ codePurity(rest), tpe)
      }
    }

    def b2c(b: Boolean): Code = if (b) trueCode else falseCode
    def b2sig(b: Boolean): Signature = if (b) trueSig else falseSig

    val assmChkPurity: Purity = if (opts.assumeChecked) Pure else Impure

    // TODO: Pour les cas ou on a besoin d'une réponse "tout de suite" pr la purity pour procéder à des simplification, comment s'y prendre???
    // TODO: Il y a des simpl. en plus que Stainless fait
    def simplifySigTopLvl(sig: Signature, tpe: Type)(using Subst): (Signature, Purity) = {
      lazy val zero = codeOfIntLit(0, tpe)
      lazy val one = codeOfIntLit(1, tpe)
      lazy val zeroSig = code2sig(zero)
      lazy val oneSig = code2sig(one)

      sig match {
        case Signature(Label.Assume, Seq(pred, body)) =>
          if (pred == trueCode) (code2sig(body), codePurity(body))
          else if (pred == falseCode) (Signature(Label.Assume, Seq(falseCode, body)), Impure)
          else (sig, Impure)

        case Signature(Label.Assert, Seq(pred, body)) =>
          val pBody = codePurity(body)
          if (pred == trueCode) (code2sig(body), pBody)
          else if (pred == falseCode) (Signature(Label.Assert, Seq(falseCode, body)), assmChkPurity ++ pBody) // Purity comme Stainless
          else (sig, assmChkPurity ++ pBody) // Ditto

        case Signature(Label.Require, Seq(pred, body)) =>
          val pBody = codePurity(body)
          if (pred == trueCode) (code2sig(body), pBody)
          else (sig, assmChkPurity ++ pBody)

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          code2sig(pred) match {
            case Signature(Label.Lambda(1), Seq(`trueCode`)) => (code2sig(body), codePurity(body))
            case _ => (sig, Impure)
          }

        // TODO: Voir ce qu'on peut faire de plus?
//        case Signature(Label.MatchExpr(patterns), scrut +: cases) =>
//          ???

        case Signature(Label.Let, Seq(e, body)) =>
          // TODO: Peut-on faire autre chose???
          // TODO: Cette histoire de vd dans lambda???
          //  -> Ah, mais c'est peut-être pour éviter une explosion en cas de lambda inlining?
          //  Hmmm, on devra p-e gérer ça dans le "uncodeOf"? Ou du moins l'opti intermédiaire...
          // TODO: Cette histoire de inline lambda???
          (sig, codePurity(e) ++ codePurity(body))

        case Signature(Label.IfExpr, Seq(cond, thenn, elze)) =>
          val pCond = codePurity(cond)
          val pThen = codePurity(thenn)
          val pElse = codePurity(elze)
          val purity = pCond ++ pThen ++ pElse

          // Note: on check la purity de `else` parce que c'est elle qu'on va dropper
          // TODO: On peut faire des trucs comme ifExpr
          if (pCond.isPure) {
            if (pElse.isPure && cond == trueCode) (code2sig(thenn), pThen)
            else if (pThen.isPure && cond == falseCode) (code2sig(elze), pElse)
            else if (thenn == elze) {
              assert(pThen == pElse)
              (code2sig(thenn), pThen)
            }
            else (sig, purity)
          }
          else (code2sig(thenn), code2sig(elze)) match {
            case (Signature(Label.IfExpr, Seq(cond2, thenn2, elze2)), _) if elze == elze2 =>
              val combinedCond = conjunct(Set(cond, cond2))
              val sig2 = Signature(Label.IfExpr, Seq(combinedCond, thenn2, elze2))
              simplifySigTopLvl(sig2, tpe)
            case (_, Signature(Label.IfExpr, Seq(cond2, thenn2, elze2))) if thenn == thenn2 =>
              val combinedCond = simplifiedDisjunction(Set(cond, cond2))
              val sig2 = Signature(Label.IfExpr, Seq(combinedCond, thenn2, elze2))
              simplifySigTopLvl(sig2, tpe)
            case _ => (sig, purity)
          }

        case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
          val purity = codePurity(e)
          isConstructor(e, adt, id) match {
            case Some(b) if purity.isPure => (b2sig(b), Pure)
            case Some(b) =>
              (Signature(Label.Let, Seq(e, b2c(b))), purity)
            case None => (sig, purity)
          }

        case Signature(Label.ADTSelector(_, ctor, sel), Seq(e)) =>
          // TODO: Cette histoire de ADT invariant?
          // TODO: Cette histoire de ADT invariant?
          // TODO: Cette histoire de ADT invariant?
          // TODO: approche un peu différente de SWP
          code2sig(e) match {
            // TODO: A-t-on de toute façon id == ctor.id ?
            case Signature(Label.ADT(id, _), args) =>
              assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
              val index = ctor.definition.selectorID2Index(sel)
              // Les args qui ne sont pas pures doivent être let-bound
              val toBeBound = args.zipWithIndex.filter { case (c, i) => i != index && !codePurity(c).isPure }.map(_._1)
              // Le résultat de la selection
              val selRes = args(index)
              val resWithBdgs = toBeBound.foldRight(selRes) {
                case (arg, rest) =>
                  val p = codePurity(arg) ++ codePurity(rest)
                  updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
              }
              (code2sig(resWithBdgs), codePurity(resWithBdgs))
            case _ =>
              // TODO: Cette histoire de ADT invariant?
              (sig, codePurity(e) ++ (if (opts.assumeChecked) Pure else Impure)) // TODO: Ok avec assumeChecked?
          }

        case Signature(Label.ADT(id, tps), args) =>
          // TODO: Cette histoire de ADT invariant?
          // TODO: Cette histoire de ADT invariant?
          // TODO: Cette histoire de ADT invariant?

          // Simplification de ADT(base.fld1, base.fld2, etc.) en base si base est de meme nature que l'adt construite
          val ctor: TypedADTConstructor = getConstructor(id, tps)
          val bases: Seq[Code] = ctor.fields.zip(args.map(code2sig)).collect {
            case (vd, Signature(Label.ADTSelector(_, ctor2, sel), Seq(base)))
              if vd.id == sel && ctor == ctor2 => base
          }
          val newAdt = bases match {
            case base +: basesRest
              // TODO: N'y a-t-il pas un risque de code duplication??? Ou pourrait-on gérer ce prob. lorsque l'on fera le "uncodeOf"???
              // TODO: Pas seulement ça, mais on risque de dupliquer "a tort" base non (problematique si impure)???
              // TODO: Orig fait e.getType == adt.getType, mais nous on fait ctor == ctor2, est-ce que ça va aussi?
              if bases.size == args.size &&
                basesRest.forall(_ == base) &&
                isConstructor(base, ADTType(id, tps), id) == Some(true) =>
              // Comme pour ADTSelector, les args qui ne sont pas pures doivent être let-bound
              val toBeBound = basesRest.filter(c => !codePurity(c).isPure)
              // On bind toBeBound et on retourne `base` (en foldant dessus)
              // let _ = toBeBound in base
              val resWithBdgs = toBeBound.foldRight(base) {
                case (arg, rest) =>
                  val p = codePurity(arg) ++ codePurity(rest)
                  updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
              }
              code2sig(resWithBdgs)
            case _ =>
              sig
          }
          val argsPurity = fold(args.map(codePurity))
          // TODO: Commentaire au sujet de opts.assumeChecked || !isImpureExpr(newAdt)
          //  en gros, les base.fld1 seront marqué pures si isCtor est vrai, donc l'adt invariant
          //  peut venir a disparaitre si on marque cette ADT(..) comme pur aussi
          // TODO: Mais puisqu'on a `base`, on doit bien avoir l'adt invariant (que ce soit par param ou ailleurs) non?
          val consingPurity = {
            if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
            else Impure
          }
          (newAdt, argsPurity ++ consingPurity)

        case Signature(Label.TupleSelect(i), Seq(e)) =>
          (code2sig(e), codePurity(e)) match {
            case (Signature(Label.Tuple, args), p) =>
              // Comme pour ADTSelector, les args qui ne sont pas pures doivent être let-bound
              val toBeBound = args.zipWithIndex.filter { case (c, j) => i != j && !codePurity(c).isPure }.map(_._1)
              // let _ = toBeBound in args(i)
              val resWithBdgs = toBeBound.foldRight(args(i)) {
                case (arg, rest) =>
                  val p = codePurity(arg) ++ codePurity(rest)
                  updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
              }
              (code2sig(resWithBdgs), p)
            case (_, p) => (sig, p)
          }

        case Signature(Label.Application, callee +: args) =>
          // TODO: On suppose que si callee est originellement let-bound, alors son occurence est de 1 (pr éviter explosion d'inlining)
          // TODO: Opti
          // TODO: Pureté?
          (sig, assmChkPurity ++ fold(args.map(codePurity)))

        case Signature(Label.Choose, Seq(`trueCode`)) if hasInstance(tpe) == Some(true) => (sig, Pure)
        case Signature(Label.Choose, Seq(_)) => (sig, Impure) // TODO: simp choose
        case Signature(Label.Forall(_), Seq(pred)) => (sig, codePurity(pred)) // TODO: simp forall

        case Signature(Label.Equals | Label.GreaterEquals | Label.LessEquals, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (trueSig, Pure) }
          else (sig, p1 ++ p2)

        case Signature(Label.LessThan | Label.GreaterThan, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (falseSig, Pure) }
          else (sig, p1 ++ p2)

        case Signature(Label.UMinus, Seq(e)) =>
          code2sig(e) match {
            case Signature(Label.UMinus, Seq(e2)) => (code2sig(e2), codePurity(e2))
            case sig => (sig, codePurity(e))
          }

        case Signature(Label.Plus, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
          else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
          else (sig, p1 ++ p2)

        case Signature(Label.Minus, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (zeroSig, Pure) }
          else (sig, p1 ++ p2)

        case Signature(Label.Times, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); (zeroSig, Pure) }
          else if (e1 == one) { assert(p1.isPure); (code2sig(e2), p2) }
          else if (e2 == one) { assert(p2.isPure); (code2sig(e1), p1) }
          else (sig, p1 ++ p2)

        case Signature(Label.Division | Label.Remainder | Label.Modulo, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (opts.assumeChecked && e2 != zero && e1 == zero && p2.isPure) { assert(p1.isPure); (zeroSig, Pure) }
          else if (opts.assumeChecked && e2 != zero && e1 == e2 && p1.isPure) { assert(p2.isPure); (oneSig, Pure) }
          else (sig, assmChkPurity ++ p1 ++ p2)

        case Signature(Label.BVNot, Seq(e)) =>
          code2sig(e) match {
            case Signature(Label.BVNot, Seq(e2)) => (code2sig(e2), codePurity(e2))
            case sig => (sig, codePurity(e))
          }

        case Signature(Label.BVAnd, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (code2sig(e1), Pure) }
          else if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); (zeroSig, Pure) }
          else (sig, p1 ++ p2)

        case Signature(Label.BVOr, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (code2sig(e1), Pure) }
          else if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
          else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
          else (sig, p1 ++ p2)

        case Signature(Label.BVXor, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); (zeroSig, Pure) }
          else if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
          else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
          else (sig, p1 ++ p2)

        case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e2 == zero) {assert(p2.isPure); (code2sig(e1), p1) }
          else (sig, p1 ++ p2)

        case sig =>
          println("What is this: "+sig)
          ???
      }
    }

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

    /*
    private val nbOccurrencesCache = mutable.Map.empty[(Code, Code), Int]

    // TODO: Et pour les indexed vars???
    def nbOccurrences(hay: Code, needle: Code): Int = {
      if (hay == needle) 1 // How can a stack of hay be a needle? Hmm...
      else nbOccurrencesCache.getOrElseUpdate((hay, needle), {
        val Signature(_, children) = code2sig(hay)
        children.map(nbOccurrences(_, needle)).sum
      })
    }

    private val substCodeCache = mutable.Map.empty[(Code, Map[Code, Code]), Code]

    // TODO: !!!! Et les indexed var ??? On ne voudra pas toutes les subst ou bien ??? !!!!
    def substCode(c: Code, subst: Map[Code, Code]): Code = {
      subst.get(c) match {
        case Some(newC) => return newC
        case None => ()
      }
      val cached = substCodeCache.get((c, subst))
        .orElse {
          substCodeCache.find { case ((_, candSubst), _) => subst.keySet.subsetOf(candSubst.keySet) }
            .map(_._2)
        }
      cached match {
        case Some(c) => return c
        case None => ()
      }

      // TODO: Un subst comme ça ne permettra pas de bénéficier d'eventuelles simplifications!!!!
      val Signature(label, children) = code2sig(c)
      val substedChildren = children.map(substCode(_, subst))
      if (children == substedChildren) c
      else {
        // TODO: Purity ok???
        // TODO: En gros, le codePurity de c permet de dire d'avoir une idée de la purity pour ce label là.
        val newPurity = codePurity(c) ++ fold(substedChildren.map(codePurity))
        val newSig = Signature(label, substedChildren)
        updateCodesSig(newSig, newPurity)
      }
    }
    */

    case class RevEnv(nestingLevel: Int)
    case class Count(occurrences: Int, inLambda: Boolean, containsLambda: Boolean, noPC: Boolean) {
      def ++(other: Count): Count =
        Count(occurrences + other.occurrences,
          inLambda || other.inLambda,
          containsLambda || other.containsLambda,
          noPC && other.noPC)
    }
    case class Counts(cts: Map[Int, Count]) {
      def ++(other: Counts): Counts = ???
    }
    object Counts {
      def empty: Counts = Counts(Map.empty)
    }
    case class Holed(expr: Map[Int, Expr] => Expr, holes: Set[Int]) {
      def plugged(ix: Int, e: Expr): Holed = {
        assert(holes.contains(ix))
        // TODO: Hmmm, ça n'a pas de sens? Ou bien?
        Holed.chkd({ subst => expr(subst.updated(ix, e)) }, holes - ix)
      }
      def plugged(ix: Int, other: Holed): Holed = {
        assert(!other.holes.contains(ix))
        Holed.chkd({ subst =>
          // TODO: Ok?
          expr(subst.updated(ix, other.expr(subst)))
        }, (holes ++ other.holes) - ix)
      }
    }
    object Holed {
      def const(e: Expr): Holed = Holed.chkd(_ => e, Set.empty)

      def ofOne(ix: Int): Holed = Holed.chkd(_(ix), Set(ix))

      def chkd(expr: Map[Int, Expr] => Expr, holes: Set[Int]): Holed = Holed({ subst =>
        assert(subst.keySet == holes)
        expr(subst)
      }, holes)

      def combined(holeds: Seq[Holed])(recons: Seq[Expr] => Expr): Holed =
        Holed.chkd({ subst =>
          val exprs = holeds.map(_.expr(subst))
          recons(exprs)
        }, holeds.flatMap(_.holes).toSet)
    }
    case class RevRes(holed: Holed, counts: Counts) {
      def ++(other: RevRes): RevRes = ???

      def countOf(ix: Int): Count = counts.cts.getOrElse(ix, Count(0, false, false, true))
    }

    def recHelper(args: Seq[Code])(recons: Seq[Expr] => Expr)(using RevEnv): RevRes = {
      val revRes = args.map(uncodeOf)
      val holed = Holed.combined(revRes.map(_.holed))(recons) // ((substs: Map[Int, Expr]) => recons(revRes.map(_.holed.expr(substs))))
      RevRes(holed, revRes.foldLeft(Counts.empty)(_ ++ _.counts))
    }

    def uncodeOf(c: Code)(using renv: RevEnv): RevRes = {
      code2sig(c) match {
        case Signature(Label.Var(v), Seq()) => RevRes(Holed.const(v), Counts.empty)
        case Signature(Label.IndexedVar(v), Seq()) =>
          val ix = v + renv.nestingLevel
          RevRes(Holed.ofOne(ix), Counts(Map(ix -> Count(1, false, false, true))))

        case Signature(Label.Let, Seq(cE, cBody)) =>
          val ix = renv.nestingLevel
          val resE = uncodeOf(cE)
          val resBody = uncodeOf(cBody)(using RevEnv(renv.nestingLevel + 1))
          val cntsInBody = resBody.countOf(???)
          val canSubstPure = codePurity(cE).isPure &&
            cntsInBody.occurrences <= 1 &&
            (!cntsInBody.inLambda || !cntsInBody.containsLambda)
          lazy val canSubstImpure = !cntsInBody.inLambda && cntsInBody.noPC && cntsInBody.occurrences == 1
          // TODO: !!!! Pas vrai le totCounts va dépendre de comment on subst !!!!
          // TODO: !!!! On n'utilise pas forcément les IndexedVar, car on fait une subst explicite dans la plupart des cas !!!!
          val totCounts: Counts = ??? // resE.counts ++ resBody.counts
          val letHoled = {
            if (canSubstPure || canSubstImpure) resBody.holed.plugged(ix, resE.holed)
            else {
              val vd = ValDef.fresh("tmp", codeTpe(cE))
              val bodyPlugged = resBody.holed.plugged(ix, vd.toVariable: Expr)
              Holed.combined(Seq(resE.holed, bodyPlugged)) { case Seq(e, b) => Let(vd, e, b) }
//              Holed({ subst =>
//                Let(vd, resE.holed.expr(subst), bodyPlugged.expr(subst))
//              }, (resE.holed.holes ++ resBody.holed.holes) - ix)
            }
          }
          RevRes(letHoled, totCounts)

        case Signature(Label.Tuple, args) =>
          recHelper(args)(Tuple.apply)

        /*
        case Signature(Label.Var(v), Seq()) => v
        case Signature(Label.IndexedVar(i), Seq()) =>
          // TODO: Il faudra "l'inverse" d'une subst
          ???
        case Signature(Label.Let, Seq(cE, cBody)) =>
          val e = uncodeOf(cE)
          ???

        case Signature(Label.Tuple, args) => Tuple(args.map(uncodeOf))
        case Signature(Label.ADT(id, tps), args) => ADT(id, tps, args.map(uncodeOf))
        case Signature(Label.ADTSelector(_, _, sel), Seq(recv)) => ADTSelector(uncodeOf(recv), sel)
        case Signature(Label.FunctionInvocation(id, tps), args) => FunctionInvocation(id, tps, args.map(uncodeOf))
        case Signature(Label.Annotated(flags), Seq(e)) => Annotated(uncodeOf(e), flags)
        case Signature(Label.IsConstructor(_, id), Seq(e)) => IsConstructor(uncodeOf(e), id)
        case Signature(Label.Assume, Seq(pred, body)) => Assume(uncodeOf(pred), uncodeOf(body))
        case Signature(Label.Assert, Seq(pred, body)) => Assert(uncodeOf(pred), None, uncodeOf(body))
        case Signature(Label.Require, Seq(pred, body)) => Require(uncodeOf(pred), uncodeOf(body))
        case Signature(Label.Ensuring, Seq(body, pred)) =>
          // Ensuring(uncodeOf(body), None, uncodeOf(pred))
          ???
        case Signature(Label.MatchExpr(pats), cScrut +: cGuardRhs) =>
          assert(2 * pats.size == cGuardRhs.size)
          val (guards, rhss) = cGuardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
          ???
        case Signature(Label.IfExpr, Seq(cond, thn, els)) => IfExpr(uncodeOf(cond), uncodeOf(thn), uncodeOf(els))
        case Signature(Label.Application, callee +: args) => Application(uncodeOf(callee), args.map(uncodeOf))
        case Signature(Label.Lambda(nbParams), Seq(body)) => ???
        case Signature(Label.Choose, Seq(pred)) => ???
        case Signature(Label.Forall(nbParams), Seq(pred)) => ???
        case Signature(Label.Or, args) => Or(args.map(uncodeOf))
        case Signature(Label.Not, Seq(c)) => Not(uncodeOf(c))

        case Signature(Label.Equals, Seq(c1, c2)) => Equals(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.LessThan, Seq(c1, c2)) => LessThan(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.GreaterThan, Seq(c1, c2)) => GreaterThan(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.LessEquals, Seq(c1, c2)) => LessEquals(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.GreaterEquals, Seq(c1, c2)) => GreaterEquals(uncodeOf(c1), uncodeOf(c2))

        case Signature(Label.UMinus, Seq(c)) => UMinus(uncodeOf(c))
        case Signature(Label.Plus, Seq(c1, c2)) => Plus(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.Minus, Seq(c1, c2)) => Minus(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.Times, Seq(c1, c2)) => Times(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.Division, Seq(c1, c2)) => Division(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.Remainder, Seq(c1, c2)) => Remainder(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.Modulo, Seq(c1, c2)) => Modulo(uncodeOf(c1), uncodeOf(c2))

        case Signature(Label.BVNot, Seq(c)) => BVNot(uncodeOf(c))
        case Signature(Label.BVAnd, Seq(c1, c2)) => BVAnd(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.BVOr, Seq(c1, c2)) => BVOr(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.BVXor, Seq(c1, c2)) => BVXor(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.BVShiftLeft, Seq(c1, c2)) => BVShiftLeft(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.BVAShiftRight, Seq(c1, c2)) => BVAShiftRight(uncodeOf(c1), uncodeOf(c2))
        case Signature(Label.BVLShiftRight, Seq(c1, c2)) => BVLShiftRight(uncodeOf(c1), uncodeOf(c2))

        case Signature(Label.BVNarrowingCast(newType), Seq(c)) => BVNarrowingCast(uncodeOf(c), newType)
        case Signature(Label.BVWideningCast(newType), Seq(c)) => BVWideningCast(uncodeOf(c), newType)
        case Signature(Label.BVUnsignedToSigned, Seq(c)) => BVUnsignedToSigned(uncodeOf(c))
        case Signature(Label.BVSignedToUnsigned, Seq(c)) => BVSignedToUnsigned(uncodeOf(c))

        case Signature(Label.Lit(lit), Seq()) => lit

        case Signature(Label.TupleSelect(index), Seq(c)) => TupleSelect(uncodeOf(c), index)
        case Signature(Label.FiniteSet(base), args) => FiniteSet(args.map(uncodeOf), base)
        case Signature(Label.FiniteArray(base), args) => FiniteArray(args.map(uncodeOf), base)
        case Signature(Label.LargeArray(elemsIndices, base), elems :+ default :+ size) =>
          LargeArray(elemsIndices.zip(elems.map(uncodeOf)).toMap, uncodeOf(default), uncodeOf(size), base)
        case Signature(Label.ArraySelect, Seq(arr, i)) => ArraySelect(uncodeOf(arr), uncodeOf(i))
        case Signature(Label.ArrayUpdated, Seq(arr, i, v)) => ArrayUpdated(uncodeOf(arr), uncodeOf(i), uncodeOf(v))
        case Signature(Label.ArrayLength, Seq(arr)) => ArrayLength(uncodeOf(arr))
*/
        case sig =>
          sys.error(s"What is this: $sig")
      }
    }

    def unAnd(e: Expr): Seq[Expr] = e match {
      case And(es) => es.flatMap(unAnd)
      case e => Seq(e)
    }

    def unOr(e: Expr): Seq[Expr] = e match {
      case Or(es) => es.flatMap(unOr)
      case e => Seq(e)
    }

    def sizeOf(e: Expr): Int = {
      def rec(e: Expr): Int = {
        sizeCache.getOrElse(e, {
          val Operator(es, _) = e
          1 + es.size + es.map(rec).sum
        })
      }
      sizeCache.getOrElseUpdate(e, rec(e))
    }
  }

}
