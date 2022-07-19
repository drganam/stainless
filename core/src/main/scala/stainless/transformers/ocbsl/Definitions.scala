package stainless
package transformers
package ocbsl

import inox.solvers

trait Definitions {
  val trees: ast.Trees
  val symbols: trees.Symbols

  import trees._
  import symbols.{given, _}

  // TODO: Si on fait un summon[Ordering[Int]] dans Opaques, ça loop...
  private val intOrdering = summon[Ordering[Int]]

  object Opaques {
    // These opaques are defined here to avoid accidental conversion from Int to Code, etc.
    opaque type Code = Int

    object Code {
      def fromInt(i: Int): Code = i
    }

//    opaque type BinderIx = Int
//
//    object BinderIx {
//      def fromScopeLevel(scopeLevel: Int): BinderIx = scopeLevel
//    }
//    extension (bIx: BinderIx) {
//      def toVarIx(scopeLevel: Int): VarIx = {
//        assert(bIx < scopeLevel, s"$bIx >= $scopeLevel")
//        scopeLevel - bIx
//      }
//    }

    opaque type VarId = Int

    object VarId {
      def fromInt(i: Int): VarId = i
    }

//    extension (vIx: VarIx) {
//      def toBinderIx(scopeLevel: Int): BinderIx = {
//        assert(vIx <= scopeLevel, s"$vIx > $scopeLevel")
//        scopeLevel - vIx
//      }
//    }

    given Ordering[Code] = intOrdering
//    given Ordering[BinderIx] = intOrdering
    given Ordering[VarId] = intOrdering
  }
  import Opaques.{given, _}

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: S'assurer que les position ou autre info n'influence pas == sur Label
  enum Label {
//    case Var(v: Variable)
    case Var(v: VarId)
    case Let(v: VarId)
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
    case Decreases

    case MatchExpr(patterns: Seq[LabelledPattern])
    case IfExpr
    case Application
    case Lambda(params: Seq[VarId])
    case Choose(v: VarId)
    case Forall(params: Seq[VarId])

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

    case StringConcat
    case SubString
    case StringLength

    case FiniteSet(base: Type)
    case SetAdd
    case ElementOfSet
    case SubsetOf
    case SetIntersection
    case SetUnion
    case SetDifference

    case FiniteBag(base: Type)
    case BagAdd
    case MultiplicityInBag
    case BagIntersection
    case BagUnion
    case BagDifference

    case FiniteMap(keyTpe: Type, valueTpe: Type)
    case MapApply
    case MapUpdated
    case MapMerge

    case FiniteArray(base: Type)
    // TODO: Comme args, il y a elems.values ++ Seq(default, size)
    //  On utilise indices pour reconstruire elems
    case LargeArray(elemsIndices: Seq[Int], base: Type)
    case ArraySelect
    case ArrayUpdated
    case ArrayLength

    case Error(tpe: Type, description: String)
    case NoTree(tpe: Type)

    def isLambda: Boolean = this match {
      case Lambda(_) => true
      case _ => false
    }

    def isDecreases: Boolean = this match {
      case Decreases => true
      case _ => false
    }
  }
  object Label {
    type AssumeLike = Label.Assume.type | Label.Assert.type | Label.Require.type | Label.Decreases.type
  }

  case class Signature(label: Label, children: Seq[Code])

  // TODO: "scrut" sert à la fois de scrut et de binder. En gros, cela réfère au node qui est scrutineed
  //  (pour les subpattern, ce sera un node a.c. un ADTSelector/TupleSelect etc.)
  enum LabelledPattern(val scrut: Code) {
    case Wildcard(scrut0: Code) extends LabelledPattern(scrut0)
    case ADT(scrut0: Code, id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern]) extends LabelledPattern(scrut0)
    case TuplePattern(scrut0: Code, sub: Seq[LabelledPattern]) extends LabelledPattern(scrut0)
    case Lit[T](scrut0: Code, lit: Literal[T]) extends LabelledPattern(scrut0)
    // TODO: What is recs???
    case Unapply(scrut0: Code, recs: Seq[Code], id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern]) extends LabelledPattern(scrut0)

    import LabelledPattern._
    def allPatterns: Seq[LabelledPattern] = Seq(this) ++ (this match {
      case Wildcard(_) => Seq.empty
      case ADT(_, _, _, sub) => sub.flatMap(_.allPatterns)
      case TuplePattern(_, sub) => sub.flatMap(_.allPatterns)
      case Lit(_, _) => Seq.empty
      case Unapply(_, _, _, _, sub) => sub.flatMap(_.allPatterns)
    })
  }

  case class LabMatchCase(pattern: LabelledPattern, guard: Code, rhs: Code)

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  enum Purity {
    case Pure
    // TODO: Ajouter "letBound": cela permet de drop l'expression (dont la sous-partie impure est let-bound à une var)
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

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def mkVar(v: VarId): Signature = Signature(Label.Var(v), Seq.empty)
  def mkLet(v: VarId, e: Code, body: Code): Signature = Signature(Label.Let(v), Seq(e, body))
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
  def mkDecreases(measure: Code, body: Code): Signature = Signature(Label.Decreases, Seq(measure, body))
  def mkMatchExpr(scrut: Code, cases: Seq[LabMatchCase]): Signature = {
    assert(cases.nonEmpty)
    val (pats, guards, rhs) = cases.map(mc => (mc.pattern, mc.guard, mc.rhs)).unzip3
    Signature(Label.MatchExpr(pats), scrut +: guards.zip(rhs).flatMap((g, r) => Seq(g, r)))
  }
  def mkIfExpr(cond: Code, thn: Code, els: Code): Signature = Signature(Label.IfExpr, Seq(cond, thn, els))
  def mkApp(callee: Code, args: Seq[Code]): Signature = Signature(Label.Application, callee +: args)
  def mkLambda(params: Seq[VarId], body: Code): Signature = Signature(Label.Lambda(params), Seq(body))
  def mkWickedChoose(v: VarId, pred: Code): Signature = Signature(Label.Choose(v), Seq(pred))
  def mkForall(params: Seq[VarId], pred: Code): Signature = Signature(Label.Forall(params), Seq(pred))
  def mkOr(es: Seq[Code]): Signature = {
    assert(es.size >= 2)
    Signature(Label.Or, es)
  }
  def mkNot(e: Code): Signature = Signature(Label.Not, Seq(e))
  def mkEquals(e1: Code, e2: Code): Signature = Signature(Label.Equals, Seq(e1, e2))
  def mkLessThan(e1: Code, e2: Code): Signature = Signature(Label.LessThan, Seq(e1, e2))
  def mkGreaterThan(e1: Code, e2: Code): Signature = Signature(Label.GreaterThan, Seq(e1, e2))
  def mkLessEquals(e1: Code, e2: Code): Signature = Signature(Label.LessEquals, Seq(e1, e2))
  def mkGreaterEquals(e1: Code, e2: Code): Signature = Signature(Label.GreaterEquals, Seq(e1, e2))
  def mkUMinus(e: Code): Signature = Signature(Label.UMinus, Seq(e))
  def mkPlus(e1: Code, e2: Code): Signature = Signature(Label.Plus, Seq(e1, e2))
  def mkMinus(e1: Code, e2: Code): Signature = Signature(Label.Minus, Seq(e1, e2))
  def mkTimes(e1: Code, e2: Code): Signature = Signature(Label.Times, Seq(e1, e2))
  def mkDivision(e1: Code, e2: Code): Signature = Signature(Label.Division, Seq(e1, e2))
  def mkRemainder(e1: Code, e2: Code): Signature = Signature(Label.Remainder, Seq(e1, e2))
  def mkModulo(e1: Code, e2: Code): Signature = Signature(Label.Modulo, Seq(e1, e2))
  def mkBVNot(e: Code): Signature = Signature(Label.BVNot, Seq(e))
  def mkBVAnd(e1: Code, e2: Code): Signature = Signature(Label.BVAnd, Seq(e1, e2))
  def mkBVOr(e1: Code, e2: Code): Signature = Signature(Label.BVOr, Seq(e1, e2))
  def mkBVXor(e1: Code, e2: Code): Signature = Signature(Label.BVXor, Seq(e1, e2))
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
  def mkSetAdd(set: Code, elem: Code): Signature = Signature(Label.SetAdd, Seq(set, elem))
  def mkElementOfSet(elem: Code, set: Code): Signature = Signature(Label.ElementOfSet, Seq(elem, set))
  def mkSubsetOf(lhs: Code, rhs: Code): Signature = Signature(Label.SubsetOf, Seq(lhs, rhs))
  def mkSetIntersection(lhs: Code, rhs: Code): Signature = Signature(Label.SetIntersection, Seq(lhs, rhs))
  def mkSetUnion(lhs: Code, rhs: Code): Signature = Signature(Label.SetUnion, Seq(lhs, rhs))
  def mkSetDifference(lhs: Code, rhs: Code): Signature = Signature(Label.SetDifference, Seq(lhs, rhs))

  def mkFiniteArray(elems: Seq[Code], base: Type): Signature = Signature(Label.FiniteArray(base), elems)
  def mkLargeArray(elems: Map[Int, Code], default: Code, size: Code, base: Type): Signature = {
    val (elemsIndices, elemsCodes) = elems.toSeq.sortBy(_._1).unzip
    Signature(Label.LargeArray(elemsIndices, base), elemsCodes ++ Seq(default, size))
  }
  def mkArraySelect(arr: Code, i: Code): Signature = Signature(Label.ArraySelect, Seq(arr, i))
  def mkArrayUpdated(arr: Code, i: Code, v: Code): Signature = Signature(Label.ArrayUpdated, Seq(arr, i, v))
  def mkArrayLength(arr: Code): Signature = Signature(Label.ArrayLength, Seq(arr))

  def mkStringConcat(lhs: Code, rhs: Code): Signature = Signature(Label.StringConcat, Seq(lhs, rhs))
  def mkSubString(expr: Code, start: Code, end: Code): Signature = Signature(Label.SubString, Seq(expr, start, end))
  def mkStringLength(expr: Code): Signature = Signature(Label.StringLength, Seq(expr))

  def mkFiniteBag(elems: Seq[(Code, Code)], base: Type): Signature =
    Signature(Label.FiniteBag(base), elems.flatMap { case (c1, c2) => Seq(c1, c2) })
  def mkBagAdd(bag: Code, elem: Code): Signature = Signature(Label.BagAdd, Seq(bag, elem))
  def mkMultiplicityInBag(elem: Code, bag: Code): Signature = Signature(Label.MultiplicityInBag, Seq(elem, bag))
  def mkBagIntersection(lhs: Code, rhs: Code): Signature = Signature(Label.BagIntersection, Seq(lhs, rhs))
  def mkBagUnion(lhs: Code, rhs: Code): Signature = Signature(Label.BagUnion, Seq(lhs, rhs))
  def mkBagDifference(lhs: Code, rhs: Code): Signature = Signature(Label.BagDifference, Seq(lhs, rhs))

  def mkFiniteMap(elems: Seq[(Code, Code)], default: Code, keyTpe: Type, valueTpe: Type): Signature =
    Signature(Label.FiniteMap(keyTpe, valueTpe),
      elems.flatMap { case (c1, c2) => Seq(c1, c2) } :+ default)
  def mkMapApply(map: Code, key: Code): Signature = Signature(Label.MapApply, Seq(map, key))
  def mkMapUpdated(map: Code, elem: Code, value: Code): Signature = Signature(Label.MapUpdated, Seq(map, elem, value))
  def mkMapMerge(mask: Code, map1: Code, map2: Code): Signature = Signature(Label.MapMerge, Seq(mask, map1, map2))

  def mkError(tpe: Type, description: String): Signature = Signature(Label.Error(tpe, description), Seq.empty)
  def mkNoTree(tpe: Type): Signature = Signature(Label.NoTree(tpe), Seq.empty)

  def mkAssumeLike(kind: Label.AssumeLike, pred: Code, body: Code): Signature = Signature(kind, Seq(pred, body))
}
