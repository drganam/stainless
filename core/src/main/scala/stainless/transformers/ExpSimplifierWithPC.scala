package stainless
package transformers

trait ExpSimplifierWithPC extends Transformer with stainless.transformers.SimplifierWithPC {
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

  override val pp: PathProvider[Env] = Env

  import OCBSL.{given, _}

  private val ocbslTL = ThreadLocal.withInitial(() => new OCBSL)
  private val ocbsl = ocbslTL.get()

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    val (re, pr) = e match {
      case Implies(l, r) =>
        val (rl, pl) = simplify(l, path)
        // val newPath = if (pl) path withCond rl else path
        val (rr, pr) = simplify(r, path withCond rl) // TODO: Can we add rl even if it's impure? After all, we do smth similar for if expressions...
        if (pl && pr) (implies(rl, rr).copiedFrom(e), true)
        else (Implies(rl, rr).copiedFrom(e), false)
      case _ => super.simplify(e, path)
    }

//    println("============================")
//    println(s"Simplification de $e:")
//    println(s"Donné $path:")
//    println(s"    pure = $pr")
//    println(s"    simp = $re")
//    println("============================")
    (re, pr)
  }


  case class Env(conditions: Set[Code], exprSubst: Map[Variable, Expr], exprCode: Map[Variable, Code]) extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = p match {
      // TODO: Qq binding ajouté
      // TODO: Pk n'ajoute-t-on pas tous les bdgs?
      //  ~> p-e parce que le Let case n'exploite pas ces infos?
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda | _: FiniteArray | _: LargeArray)) =>
        val c = ocbsl.codeOf(expr)(using Subst(exprCode))
        Env(conditions, exprSubst + (vd.toVariable -> expr), exprCode + (vd.toVariable -> c))
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) {
          val c = ocbsl.codeOf(exp)(using Subst(exprCode))
          Env(conditions, exprSubst + (vd.toVariable -> exp), exprCode + (vd.toVariable -> c))
        } else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = this

    // TODO: On pourra supposer que cond a été simplifié avant
    // TODO: Et si cond est impure???
    override def withCond(cond: Expr): Env = {
      val codeCond = ocbsl.codeOf(cond)(using Subst(exprCode))
//      println("============================")
//      println(s"Donné $cond")
//      println(s"Code pour $cond   ~~>   $codeCond")
//      println("============================")
      Env(conditions + codeCond, exprSubst, exprCode)
    }

    override def negate: Env = Env(Set(ocbsl.negatedConjunction(conditions)), exprSubst, exprCode)

    override def merge(that: Env): Env = Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst, exprCode ++ that.exprCode)

    // TODO: Voir ou est-ce que ce truc est utilisé
    override def expand(expr: Expr): Expr = expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }

    // TODO: Peut-on supposer que expr a été simplifié??? Il semblerait que non!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    override def implies(expr: Expr): Boolean = {
      if (expr.getType != BooleanType()) false
      else ocbsl.implies(conditions, ocbsl.codeOf(expr)(using Subst(exprCode)))
    }
  }

  object Env extends PathProvider[Env] {
    def empty: Env = Env(Set.empty, Map.empty, Map.empty)
  }

  override def initEnv: Env = Env.empty

  // TODO: Le gag: comment repr. un lambda? Car la sol. naive semble fausse!!!
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

    // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

    private val codes = mutable.Map.empty[Expr, Code]
    private val sig2code = mutable.Map.empty[Signature, Code]
    private val code2sig = mutable.Map.empty[Code, Signature]
    private val sizeCache = mutable.Map.empty[Expr, Int]

    private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
    private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
    private val falseCode = updateCodesSig(falseSig)
    private val trueCode = updateCodesSig(trueSig)

    private var unknownCounter = 0

    def codeOf(e: Expr)(using Subst): Code = codes.getOrElseUpdate(e, {
      // TODO: ok?
      val pDisjRes = pDisj(e)
      simplifiedDisjunction(pDisjRes.toSet)
    })

    // TODO: Pk ce truc est fait dans codeOf mais pas dans pDisj?
    def simplifiedDisjunction(disj: Set[Code]): Code = {
      // TODO: Caching?
      val disj1 = disj.filter(_ != falseCode)
      if (disj1.isEmpty) falseCode
      else if (disj1.size == 1) disj1.head
      else if (disj1.contains(trueCode) || checkForContradiction(disj1)) trueCode
      else {
        val sig = Signature(Label.Or, disj1.toSeq.sorted)
        updateCodesSig(sig)
      }
    }

    def implies(lhs: Set[Code], rhs: Code): Boolean = {
      assert(lhs.forall(code2sig.contains))
      assert(code2sig.contains(rhs))
      if (lhs.isEmpty) rhs == trueCode
      else {
        // a ==> b === a && b = a
        val lhsConj = conjunct(lhs)
        val rhsLhsConj = conjunct(Set(lhsConj, rhs))
        rhsLhsConj == lhsConj
      }
    }

    def conjunct(conj: Set[Code]): Code = {
      updateCodesSig(pNegNormal(negatedConjunction(conj)))
    }

    def negatedConjunction(conj: Set[Code]): Code = {
      // TODO: Caching?
      val negDisj = conj.map(c => updateCodesSig(pNegNormal(c)))
      simplifiedDisjunction(negDisj)
    }

    def checkForContradiction(disj: Set[Code]): Boolean = {
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
        case Signature(Label.Or, children) => children
        case sig => Seq(updateCodesSig(sig))
      }
    }

    // TODO: Signature de Not(child)
    def pNeg(child: Expr)(using Subst): Signature = {
      codes.get(child) match {
        case Some(c) => return pNegNormal(c)
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
            .distinct.sorted
          if (r.isEmpty) pNeg(ors1.head) // TODO: Caching?
          else {
            // TODO: Ok?
            // TODO: Ressemble pas mal à simplifiedDisjunction
            val s = (pDisj(ors1.head) ++ r)
              .filter(_ != falseCode)
              .distinct.sorted
            if (s.contains(trueCode) || checkForContradiction(s.toSet)) falseSig
            else if (s.size == 1) pNegNormal(s.head) // TODO: Ok?
            else {
              val orCode = updateCodesSig(Signature(Label.Or, s))
              Signature(Label.Not, Seq(orCode))
            }
          }
        case _ =>
          // TODO: Ok?
          computeSignature(child) match {
            case Signature(Label.Lit(BooleanLiteral(b)), Seq()) =>
              Signature(Label.Lit(BooleanLiteral(!b)), Seq.empty)
            case sig =>
              // TODO: Ok?
              Signature(Label.Not, Seq(sig2code(sig)))
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

    // TODO: Est-ce correct de faire ça?
    def computeSignature(e: Expr)(using subst: Subst): Signature = {
      codes.get(e).map(code2sig) match {
        case Some(sig) => return sig
        case None => ()
      }

      lazy val zero = codeOfIntLit(0, e.getType)
      lazy val one = codeOfIntLit(1, e.getType)
      lazy val zeroSig = code2sig(zero)
      lazy val oneSig = code2sig(one)

      // TODO: Check label (pour voir s'il n'y a pas d'erreur de copié/collé)
      val sig = e match {
        case v: Variable =>
          subst.free.get(v).map(code2sig) // Check if `v` is a "free" variable (free w.r.t. OCBSL, but bound w.r.t. Env)
            // Check if `v` is bound to a let-binding
            .orElse(subst.bound.get(v).map { i =>
              val sig = Signature(Label.IndexedVar(subst.nestingLevel - i), Seq.empty)
              updateCodesSig(sig)
              sig
            })
            .getOrElse(Signature(Label.Var(v), Seq.empty))
        case Tuple(args) =>
          Signature(Label.Tuple, args.map(codeOf))
        case ADT(id, tps, args) =>
          Signature(Label.ADT(id, tps), args.map(codeOf))
        case ADTSelector(e, selector) =>
          Signature(Label.ADTSelector(selector), Seq(codeOf(e)))
        case FunctionInvocation(id, tps, args) =>
          Signature(Label.FunctionInvocation(id, tps), args.map(codeOf))


        case IsConstructor(e, id) =>
          Signature(Label.IsConstructor(id), Seq(codeOf(e)))
        case IfExpr(cond, thenn, elze) =>
          // TODO: In case of purity, we can simplify things, akin to what is done in SimplifierWithPC...
          Signature(Label.IfExpr, Seq(codeOf(cond), codeOf(thenn), codeOf(elze)))
        case Application(callee, args) =>
          Signature(Label.Application, Seq(codeOf(callee)) ++ args.map(codeOf))

        case Let(vd, e, body) =>
          val cE = codeOf(e)
          val newSubst = Subst(subst.free, subst.bound + (vd.toVariable -> subst.nestingLevel), subst.nestingLevel + 1)
          val cB = codeOf(body)(using newSubst)
          Signature(Label.Let, Seq(cE, cB))

        case Lambda(params, body) =>
          // Note: params may be empty, which is fine (the nesting level will not increase)
          val newSubst = Subst(subst.free,
            subst.bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> (subst.nestingLevel + i)).toMap,
            subst.nestingLevel + params.size)
          val c = Seq(codeOf(body)(using newSubst))
          Signature(Label.Lambda, c)

        case Choose(res, pred) =>
          val newSubst = Subst(subst.free, subst.bound + (res.toVariable -> subst.nestingLevel), subst.nestingLevel + 1)
          Signature(Label.Choose, Seq(codeOf(pred)(using newSubst)))

        case Forall(params, body) =>
          val newSubst = Subst(subst.free,
            subst.bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> (subst.nestingLevel + i)).toMap,
            subst.nestingLevel + params.size)
          Signature(Label.Forall, Seq(codeOf(body)(using newSubst)))

        // TODO: Problème: ces (futures) simplifications ne sont appelées que lorsque l'on fait un withCond etc. et ne font pas partie intégrante de simplify!!!
        // TODO: Problème: ces (futures) simplifications ne sont appelées que lorsque l'on fait un withCond etc. et ne font pas partie intégrante de simplify!!!

        // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
        // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
        //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
        //  une map ad-hoc qui contient ces infos...?
        case Annotated(e, flags) =>
          Signature(Label.Annotated(flags), Seq(codeOf(e)))

        // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
        case and @ And(_) =>
          val ands = unAnd(and)
          code2sig(codeOf(Not(Or(ands.map(Not.apply)))))
        case or @ Or(_) =>
          val ors = unOr(or)
          Signature(Label.Or, ors.map(codeOf).sorted) // TODO: checkForContradiction?
        case Not(e) => pNeg(e)
        case Implies(e1, e2) =>
          code2sig(codeOf(Or(Not(e1), e2)))

        // TODO: Are we actually allowed to do these simp.? After all, they may be impure expressions...

        case Equals(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) trueSig
          else Signature(Label.Equals, Seq(c1, c2).sorted)
        case LessThan(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) falseSig
          else Signature(Label.LessThan, Seq(c1, c2))
        case GreaterThan(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) falseSig
          else Signature(Label.GreaterThan, Seq(c1, c2))
        case LessEquals(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) trueSig
          else Signature(Label.LessEquals, Seq(c1, c2))
        case GreaterEquals(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) trueSig
          else Signature(Label.GreaterEquals, Seq(c1, c2))

        case UMinus(UMinus(e)) =>
          code2sig(codeOf(e))
        case UMinus(e) =>
          Signature(Label.UMinus, Seq(codeOf(e)))
        case Plus(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == zero) code2sig(c2)
          else if (c2 == zero) code2sig(c1)
          else Signature(Label.Plus, Seq(c1, c2).sorted)
        case Minus(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) code2sig(codeOfIntLit(0, e.getType))
          else Signature(Label.Minus, Seq(c1, c2))
        case Times(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == zero || c2 == zero) zeroSig
          else if (c1 == one) code2sig(c2)
          else if (c2 == one) code2sig(c1)
          else Signature(Label.Times, Seq(c1, c2).sorted)
        case Division(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == zero) zeroSig
          else if (c1 == c2) oneSig
          else Signature(Label.Division, Seq(c1, c2))
        case Remainder(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) zeroSig
          else Signature(Label.Remainder, Seq(c1, c2))
        case Modulo(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) zeroSig
          else Signature(Label.Modulo, Seq(c1, c2))

        case BVNot(BVNot(e)) =>
          code2sig(codeOf(e))
        case BVNot(e) =>
          Signature(Label.BVNot, Seq(codeOf(e)))
        case BVAnd(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) code2sig(c1)
          else if (c1 == zero || c2 == zero) zeroSig
          else Signature(Label.BVAnd, Seq(c1, c2).sorted)
        case BVOr(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) code2sig(c1)
          else if (c1 == zero) code2sig(c2)
          else if (c2 == zero) code2sig(c1)
          else Signature(Label.BVOr, Seq(c1, c2).sorted)
        case BVXor(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) zeroSig
          else if (c1 == zero) code2sig(c2)
          else if (c2 == zero) code2sig(c1)
          else Signature(Label.BVXor, Seq(c1, c2).sorted)
        case BVShiftLeft(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c2 == zero) code2sig(c1)
          else Signature(Label.BVShiftLeft, Seq(c1, c2))
        case BVAShiftRight(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c2 == zero) code2sig(c1)
          else Signature(Label.BVAShiftRight, Seq(c1, c2))
        case BVLShiftRight(e1, e2) =>
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c2 == zero) code2sig(c1)
          else Signature(Label.BVLShiftRight, Seq(c1, c2))

        case BVNarrowingCast(e, newType) =>
          Signature(Label.BVNarrowingCast(newType), Seq(codeOf(e)))
        case BVWideningCast(e, newType) =>
          Signature(Label.BVWideningCast(newType), Seq(codeOf(e)))

        case BVUnsignedToSigned(e) =>
          Signature(Label.BVUnsignedToSigned, Seq(codeOf(e)))
        case BVSignedToUnsigned(e) =>
          Signature(Label.BVSignedToUnsigned, Seq(codeOf(e)))

        case TupleSelect(e, index) =>
          Signature(Label.TupleSelect(index), Seq(codeOf(e)))

        case FiniteArray(elems, base) =>
          Signature(Label.FiniteArray(base), elems.map(codeOf))
        case LargeArray(elems, default, size, base) =>
          val elemsSorted = elems.toSeq.sortBy(_._1)
          val elemsIndices = elemsSorted.map(_._1)
          val elemsCode = elemsSorted.map((_, e) => codeOf(e))
          Signature(Label.LargeArray(elemsIndices, base), elemsCode ++ Seq(codeOf(default), codeOf(size)))
        case ArraySelect(array, index) =>
          Signature(Label.ArraySelect, Seq(codeOf(array), codeOf(index)))
        case ArrayUpdated(array, index, value) =>
          Signature(Label.ArrayUpdated, Seq(codeOf(array), codeOf(index), codeOf(value)))
        case ArrayLength(array) =>
          Signature(Label.ArrayLength, Seq(codeOf(array)))

        case l: Literal[_] =>
          Signature(Label.Lit(l), Seq.empty)

        case _ =>
          // println(s"Generated an 'unknown' for $e (with id $unknownCounter)")
          val sig = Signature(Label.Unknown(unknownCounter), Seq.empty)
          unknownCounter += 1
          sig
      }

      updateCodesSig(sig)
      sig
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

    def updateCodesSig(sig: Signature): Code = {
      sig2code.getOrElseUpdate(sig, {
        val newCode = Code.fromInt(sig2code.size)
        assert(!code2sig.contains(newCode))
        code2sig += newCode -> sig
        newCode
      })
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
