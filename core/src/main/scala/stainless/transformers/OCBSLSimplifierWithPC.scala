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
    ???
  }

  case class Env(conditions: Set[Code],
                 exprSubst: Map[Variable, Expr],
                 exprCode: Map[Variable, Code],
                 // Note: Order is important (hence Seq)
                 bound: Seq[Variable]) extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = p match {
      // TODO: Qq binding ajouté
      // TODO: Pk n'ajoute-t-on pas tous les bdgs?
      //  ~> p-e parce que le Let case n'exploite pas ces infos?
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda | _: FiniteArray | _: LargeArray)) =>
        // TODO: Quid purity???
        val (c, _) = ocbsl.codeOf(expr)(using mkSubst)
        Env(conditions, exprSubst + (vd.toVariable -> expr), exprCode + (vd.toVariable -> c), bound)
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) {
          val (c, _) = ocbsl.codeOf(exp)(using mkSubst)
          Env(conditions, exprSubst + (vd.toVariable -> exp), exprCode + (vd.toVariable -> c), bound)
        } else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = Env(conditions, exprSubst, exprCode, bound :+ vd.toVariable)

    // TODO: On pourra supposer que cond a été simplifié avant
    override def withCond(cond: Expr): Env = {
      // TODO: Et si cond est impure???
      val (codeCond, _) = ocbsl.codeOf(cond)(using mkSubst)
      Env(conditions + codeCond, exprSubst, exprCode, bound)
    }

    override def negate: Env = Env(Set(ocbsl.negatedConjunction(conditions)._1), exprSubst, exprCode, bound)

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
         ocbsl.implies(conditions, ocbsl.codeOf(expr)._1)
       }
    }

    def mkSubst: Subst = {
      val boundMap = bound.zipWithIndex.map((v, i) => v -> i).toMap
      Subst(exprCode, boundMap, boundMap.size)
    }
  }

  object Env extends PathProvider[Env] {
    def empty: Env = Env(Set.empty, Map.empty, Map.empty, Seq.empty)
  }

  override def initEnv: Env = Env.empty

  enum Label {
    case Var(v: Variable)
    case IndexedVar(i: Int)
    case Let // Indexed
    case Tuple
    case ADT(id: Identifier, tps: Seq[Type])
    case ADTSelector(selector: Identifier)
    case FunctionInvocation(id: Identifier, tps: Seq[Type])
    case Annotated(flags: Seq[Flag])
    case IsConstructor(id: Identifier)
    case IfExpr
    case Application
    case Lambda // Indexed
    case Choose // Indexed
    case Forall // Indexed

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

    case Unknown(id: Int)
  }

  // TODO: Si on fait un summon[Ordering[Int]] dans OCBSL, ça loop...
  private val intOrdering = summon[Ordering[Int]]

  object OCBSL {
    // `Code` wrapped here to avoid accidental conversion from Int to Code
    opaque type Code = Int

    object Code {
      def fromInt(i: Int): Code = i
    }

    given Ordering[Code] = intOrdering

    case class Signature(label: Label, children: Seq[Code])

    case class Subst(free: Map[Variable, Code], bound: Map[Variable, Int] = Map.empty, nestingLevel: Int = 0)
  }

  class OCBSL {
    import scala.collection.mutable
    import Purity._

    // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

    private val codes = mutable.Map.empty[Expr, Code]
    private val sig2code = mutable.Map.empty[Signature, Code]
    private val code2sig = mutable.Map.empty[Code, Signature]
    private val sizeCache = mutable.Map.empty[Expr, Int]

    private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
    private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
    private val falseCode = updateCodesSig(falseSig, Pure)
    private val trueCode = updateCodesSig(trueSig, Pure)

    private var unknownCounter = 0

    private val purityCache = mutable.Map.empty[Identifier, Boolean]
    private val codePurityCache = mutable.Map.empty[Code, Boolean]
    private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
    private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
    private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V
    private val visiting = mutable.Set.empty[Identifier]

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

    def codePurity(c: Code): Purity = {
      assert(code2sig.contains(c))
      codePurityCache.get(c)
        .map(fromBoolean)
        .getOrElse(Delayed(codeBlockedBy(c)))
    }

    def codeOf(e: Expr)(using subst: Subst): (Code, Purity) = {
      def result = {
        codes.get(e) match {
          case Some(c) =>
            (c, codePurity(c))
          case None =>
            simplifiedDisjunction(pDisj(e).toSet)
        }
      }
      e match {
        case v: Variable if subst.bound.contains(v) =>
          // TODO: Cette assertion ne tient pas --' Il semblerait qu'il manque un withBound a quelque part...
          // TODO: Est-ce que c'est qd meme ok?
          // assert(!codes.contains(v))
          result
        case _ =>
          val (c, p) = result
          // TODO: Quid purity (cache)????
          codes += e -> c
          (c, p)
      }
    }

    def exprPurity(e: Expr)(using Subst): Purity = codeOf(e)._2

    def fnPurity(fn: Identifier)(using Subst): Purity = {
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
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val res = exprPurity(getFunction(fn).fullBody)
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
    def simplifiedDisjunction(disj: Set[Code]): (Code, Purity) = {
      // TODO: Caching?
      val purity = fold(disj.map(codePurity).toSeq)
      val disj1 = disj.filter(_ != falseCode)
      if (disj1.isEmpty) (falseCode, Pure)
      else if (disj1.size == 1) (disj1.head, purity)
      else if (purity.isPure && (disj1.contains(trueCode) || checkForContradiction(disj1))) (trueCode, purity)
      else {
        val sig = Signature(Label.Or, disj1.toSeq.sorted)
        (updateCodesSig(sig, purity), purity)
      }
    }

    def computeSignature(e: Expr)(using subst: Subst): (Signature, Purity) = {
      codes.get(e).map(c => (code2sig(c), codePurity(c))) match {
        case Some((sig, purity)) => return (sig, purity)
        case None => ()
      }

      lazy val zero = codeOfIntLit(0, e.getType)
      lazy val one = codeOfIntLit(1, e.getType)
      lazy val zeroSig = code2sig(zero)
      lazy val oneSig = code2sig(one)

      // TODO: Assume, Match, Require, etc. bref, tout ce qui été géré par SimplifierWithPC!!!
      // TODO: Assume, Match, Require, etc. bref, tout ce qui été géré par SimplifierWithPC!!!
      // TODO: Env!!!!
      // TODO: Env!!!!
      // TODO: Utiliser des simplification similaires à SimplifierWithPC
      // TODO: Utiliser des simplification similaires à SimplifierWithPC
      val (sig, purity) = e match {
        case v: Variable =>
          val sig = subst.free.get(v).map(code2sig) // Check if `v` is a "free" variable (free w.r.t. OCBSL, but bound w.r.t. Env)
            // Check if `v` is bound to a let-binding
            .orElse(subst.bound.get(v).map { i =>
              val sig = Signature(Label.IndexedVar(subst.nestingLevel - i), Seq.empty)
              updateCodesSig(sig, Pure)
              sig
            })
            .getOrElse(Signature(Label.Var(v), Seq.empty))
          (sig, Pure)

        case Tuple(args) =>
          val (cs, ps) = args.map(codeOf).unzip
          (Signature(Label.Tuple, cs), fold(ps))

        // TODO: Non, voir SWP
        case ADT(id, tps, args) =>
          val (cs, ps) = args.map(codeOf).unzip
          (Signature(Label.ADT(id, tps), cs), fold(ps))

        // TODO: Non, voir SWP
        case ADTSelector(e, selector) =>
          val (c, p) = codeOf(e)
          (Signature(Label.ADTSelector(selector), Seq(c)), p)

        case FunctionInvocation(id, tps, args) =>
          val (cs, ps) = args.map(codeOf).unzip
          lazy val callPurity = {
            if (visiting.contains(id)) {
              if (!opts.assumeChecked) Impure
              else Delayed(Set(id))
            }
            else fnPurity(id)
          }
          val purity = fold(ps) ++ callPurity
          (Signature(Label.FunctionInvocation(id, tps), cs), purity)

        // TODO: Non, voir SWP
        case Application(callee, args) =>
          val (cCallee, pCallee) = codeOf(callee)
          val (cs, ps) = args.map(codeOf).unzip
          (Signature(Label.Application, cCallee +: cs), pCallee ++ fold(ps))

        // TODO: Pour les cas ou on a besoin d'une réponse "tout de suite" pour procéder à des simplification, comment s'y prendre???
        case IfExpr(cond, thenn, elze) =>
          val (cCond, pCond) = codeOf(cond)
          val (cThen, pThen) = codeOf(thenn)
          val (cElse, pElse) = codeOf(elze)
          // Note: on check la purity de `else` parce que c'est elle qu'on va dropper
          if (cCond == trueCode && pCond.isPure && pElse.isPure)
            (code2sig(cThen), pThen)
          else if (cCond == falseCode && pCond.isPure && pThen.isPure)
            (code2sig(cElse), pElse)
          else (Signature(Label.IfExpr, Seq(cCond, cThen, cElse)), pCond ++ pThen ++ pElse)

        // TODO: Utiliser qqchose de similaire à isConstructor dans SimplifierWithPC
        case IsConstructor(e, id) =>
          val (c, p) = codeOf(e)
          (Signature(Label.IsConstructor(id), Seq(c)), p)

        // TODO: Non, voir SWP
        // TODO: Ok w.r.t purité?
        // TODO: Plusieurs opti possibles
        case Let(vd, e, body) =>
          val (cE, pE) = codeOf(e)
          val newSubst = Subst(subst.free, subst.bound + (vd.toVariable -> subst.nestingLevel), subst.nestingLevel + 1)
          val (cB, pB) = codeOf(body)(using newSubst)
          (Signature(Label.Let, Seq(cE, cB)), pE ++ pB)

        // TODO: Non, voir SWP
        case Lambda(params, body) =>
          // Note: params may be empty, which is fine (the nesting level will not increase)
          val newSubst = Subst(subst.free,
            subst.bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> (subst.nestingLevel + i)).toMap,
            subst.nestingLevel + params.size)
          val (c, p) = codeOf(body)(using newSubst)
          (Signature(Label.Lambda, Seq(c)), p)

        case Choose(res, pred) =>
          val newSubst = Subst(subst.free, subst.bound + (res.toVariable -> subst.nestingLevel), subst.nestingLevel + 1)
          val (c, p) = codeOf(pred)(using newSubst)
          (Signature(Label.Choose, Seq(c)), p)

        case Forall(params, body) =>
          val newSubst = Subst(subst.free,
            subst.bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> (subst.nestingLevel + i)).toMap,
            subst.nestingLevel + params.size)
          val (c, p) = codeOf(body)(using newSubst)
          (Signature(Label.Forall, Seq(c)), p)

        // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
        // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
        //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
        //  une map ad-hoc qui contient ces infos...?
        case Annotated(e, flags) =>
          val (c, p) = codeOf(e)
          (Signature(Label.Annotated(flags), Seq(c)), p)

        // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
        case and @ And(_) =>
          val ands = unAnd(and)
          val (c, p) = codeOf(Not(Or(ands.map(Not.apply))))
          (code2sig(c), p)
        case or @ Or(_) =>
          // TODO: checkForContradiction?
          // TODO: Pas d'incohérence avec purity? (p.ex. un code qui est pure, mais pas l'autre)?
          val (cs, ps) = unOr(or).map(codeOf).sortBy(_._1).distinctBy(_._1).unzip
          (Signature(Label.Or, cs), fold(ps))
        case Not(e) => pNeg(e)
        case Implies(e1, e2) =>
          val (c, p) = codeOf(Or(Not(e1), e2))
          (code2sig(c), p)
        case Equals(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (trueSig, Pure)
          else (Signature(Label.Equals, Seq(c1, c2).sorted), p1 ++ p2)
        case LessThan(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (falseSig, Pure)
          else (Signature(Label.LessThan, Seq(c1, c2)), p1 ++ p2)
        case GreaterThan(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (falseSig, Pure)
          else (Signature(Label.GreaterThan, Seq(c1, c2)), p1 ++ p2)
        case LessEquals(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (trueSig, Pure)
          else (Signature(Label.LessEquals, Seq(c1, c2)), p1 ++ p2)
        case GreaterEquals(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (trueSig, Pure)
          else (Signature(Label.GreaterEquals, Seq(c1, c2)), p1 ++ p2)

        // TODO: On pourrait faire plus? (cf simplifyArith)
        case UMinus(UMinus(e)) =>
          val (c, p) = codeOf(e)
          // This simp. is Ok even if e is impure, as we are only "peeling off" the UMinus
          (code2sig(c), p)
        case UMinus(e) =>
          val (c, p) = codeOf(e)
          (Signature(Label.UMinus, Seq(c)), p)

        case Plus(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          // TODO: Si c1 == zero, alors p1 == Pure, n'est-ce pas? (ditto pr c2)
          if (c1 == zero) code2sig(c2)
          else if (c2 == zero) code2sig(c1)
          else (Signature(Label.Plus, Seq(c1, c2).sorted), p1 ++ p2)
        case Minus(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          // TODO: Si c1 == c2, alors les deux ont la meme purity non?
          if (c1 == c2 && p1.isPure && p2.isPure) (code2sig(codeOfIntLit(0, e.getType)), Pure)
          else (Signature(Label.Minus, Seq(c1, c2)), p1 ++ p2)
        case Times(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if ((c1 == zero || c2 == zero) && p1.isPure && p2.isPure) zeroSig
          else if (c1 == one) code2sig(c2)
          else if (c2 == one) code2sig(c1)
          else (Signature(Label.Times, Seq(c1, c2).sorted), p1 ++ p2)
        case Division(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == zero && p2.isPure) zeroSig
          else if (c1 == c2 && p1.isPure && p2.isPure) oneSig
          else (Signature(Label.Division, Seq(c1, c2)), p1 ++ p2)
        case Remainder(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) zeroSig
          else (Signature(Label.Remainder, Seq(c1, c2)), p1 ++ p2)
        case Modulo(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) zeroSig
          else (Signature(Label.Modulo, Seq(c1, c2)), p1 ++ p2)

        case BVNot(BVNot(e)) =>
          val (c, p) = codeOf(e)
          (code2sig(c), p)
        case BVNot(e) =>
          val (c, p) = codeOf(e)
          (Signature(Label.BVNot, Seq(c)), p)
        case BVAnd(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) (code2sig(c1), Pure)
          else if ((c1 == zero || c2 == zero) && p1.isPure && p2.isPure) zeroSig
          else (Signature(Label.BVAnd, Seq(c1, c2).sorted), p1 ++ p2)
        case BVOr(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) code2sig(c1)
          else if (c1 == zero) (code2sig(c2), p2)
          else if (c2 == zero) (code2sig(c1), p1)
          else (Signature(Label.BVOr, Seq(c1, c2).sorted), p1 ++ p2)
        case BVXor(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c1 == c2 && p1.isPure && p2.isPure) zeroSig
          else if (c1 == zero) (code2sig(c2), p2)
          else if (c2 == zero) (code2sig(c1), p1)
          else (Signature(Label.BVXor, Seq(c1, c2).sorted), p1 ++ p2)
        case BVShiftLeft(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c2 == zero) (code2sig(c1), p1)
          else (Signature(Label.BVShiftLeft, Seq(c1, c2)), p1 ++ p2)
        case BVAShiftRight(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c2 == zero) (code2sig(c1), p1)
          else (Signature(Label.BVAShiftRight, Seq(c1, c2)), p1 ++ p2)
        case BVLShiftRight(e1, e2) =>
          val (c1, p1) = codeOf(e1)
          val (c2, p2) = codeOf(e2)
          if (c2 == zero) (code2sig(c1), p1)
          else (Signature(Label.BVLShiftRight, Seq(c1, c2)), p1 ++ p2)

        case BVNarrowingCast(e, newType) =>
          val (c, p) = codeOf(e)
          (Signature(Label.BVNarrowingCast(newType), Seq(c)), p)
        case BVWideningCast(e, newType) =>
          val (c, p) = codeOf(e)
          (Signature(Label.BVWideningCast(newType), Seq(c)), p)

        case BVUnsignedToSigned(e) =>
          val (c, p) = codeOf(e)
          (Signature(Label.BVUnsignedToSigned, Seq(c)), p)
        case BVSignedToUnsigned(e) =>
          val (c, p) = codeOf(e)
          (Signature(Label.BVSignedToUnsigned, Seq(c)), p)

        case TupleSelect(e, index) =>
          val (c, p) = codeOf(e)
          (Signature(Label.TupleSelect(index), Seq(c)), p)

        case FiniteArray(elems, base) =>
          val (cs, ps) = elems.map(codeOf).unzip
          (Signature(Label.FiniteArray(base), cs), fold(ps))

        case LargeArray(elems, default, size, base) =>
          val elemsSorted = elems.toSeq.sortBy(_._1)
          val elemsIndices = elemsSorted.map(_._1)
          val (codeElems, purityElems) = elemsSorted.map((_, e) => codeOf(e)).unzip
          val (codeDef, purityDef) = codeOf(default)
          val (codeSz, puritySz) = codeOf(size)
          (Signature(Label.LargeArray(elemsIndices, base), codeElems ++ Seq(codeDef, codeSz)), fold(purityElems) ++ purityDef ++ puritySz)

        case ArraySelect(array, index) =>
          val (cArr, pArr) = codeOf(array)
          val (cIx, pIx) = codeOf(index)
          (Signature(Label.ArraySelect, Seq(cArr, cIx)), pArr ++ pIx)
        case ArrayUpdated(array, index, value) =>
          val (cArr, pArr) = codeOf(array)
          val (cIx, pIx) = codeOf(index)
          val (cVal, pVal) = codeOf(value)
          (Signature(Label.ArrayUpdated, Seq(cArr, cIx, cVal)), pArr ++ pIx ++ pVal)
        case ArrayLength(array) =>
          val (cArr, pArr) = codeOf(array)
          (Signature(Label.ArrayLength, Seq(cArr)), pArr)

        case l: Literal[_] =>
          (Signature(Label.Lit(l), Seq.empty), Pure)

        case _ =>
          // println(s"Generated an 'unknown' for $e (with id $unknownCounter)")
          val sig = Signature(Label.Unknown(unknownCounter), Seq.empty)
          unknownCounter += 1
          // TODO: Impure car risque de supprimer qqchose qui peut etre utile? (malgré opts.assumeChecked)
          (sig, Impure)
      }

      updateCodesSig(sig, purity)
      (sig, purity)
    }

    def implies(lhs: Set[Code], rhs: Code): Boolean = {
      assert(lhs.forall(code2sig.contains))
      assert(code2sig.contains(rhs))
      if (lhs.isEmpty) rhs == trueCode
      else {
        // TODO: Quid purité de rhs???
        // a ==> b === a && b = a
        val (lhsConj, _) = conjunct(lhs)
        val (rhsLhsConj, _) = conjunct(Set(lhsConj, rhs))
        rhsLhsConj == lhsConj
      }
    }

    def conjunct(conj: Set[Code]): (Code, Purity) = {
      val (neg, p) = negatedConjunction(conj)
      (updateCodesSig(pNegNormal(neg), p), p)
    }

    def negatedConjunction(conj: Set[Code]): (Code, Purity) = {
      // TODO: Caching?
      val negDisj = conj.map(c => updateCodesSig(pNegNormal(c), codePurity(c)))
      simplifiedDisjunction(negDisj)
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
      computeSignature(e) match {
        case (Signature(Label.Or, children), _) => children
        case (sig, p) => Seq(updateCodesSig(sig, p))
      }
    }

    // Signature de Not(child)
    def pNeg(child: Expr)(using Subst): (Signature, Purity) = {
      codes.get(child) match {
        case Some(c) => return (pNegNormal(c), codePurity(c))
        case None => ()
      }

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
              val orCode = updateCodesSig(Signature(Label.Or, s), purity)
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

    def codeOfIntLit(lit: BigInt, tpe: Type)(using Subst): Code = codeOf(intLitOfType(lit, tpe))._1

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

    def updateCodesSig(sig: Signature, purity: Purity): Code = {
      sig2code.get(sig) match {
        case Some(c) =>
          // TODO: Quid purity????
          c
        case None =>
          val newCode = Code.fromInt(sig2code.size)
          assert(!code2sig.contains(newCode))
          sig2code += sig -> newCode
          code2sig += newCode -> sig
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
