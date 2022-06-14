package stainless
package transformers

trait ExpSimplifierWithPC extends Transformer with stainless.transformers.SimplifierWithPC {
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

  override val pp: PathProvider[Env] = Env

  private val ocbsl = ThreadLocal.withInitial(() => new OCBSL)

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    // TODO: Un dernier catch-all pour boolean qu'on pourra OCBSLiser
    case _ => ???
  }

  // conditions: Set[Expr], exprSubst: Map[Variable, Expr]
  case class Env() extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = ??? /*p match {
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda)) =>
        new Env(conditions, exprSubst + (vd.toVariable -> expr))
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) new Env(conditions, exprSubst + (vd.toVariable -> exp))
        else this
      case _ => this
    }*/

    override def withBound(vd: ValDef): Env = this

    // TODO: On pourra supposer que cond a été simplifié avant
    override def withCond(cond: Expr): Env = ??? // new Env(conditions + cond, exprSubst)

    // TODO: Voir ce qu'on peut faire de ça
    override def negate: Env = ??? // new Env(Set(not(and(conditions.toSeq : _*))), exprSubst)

    override def merge(that: Env): Env = ???
//      new Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst)

    // TODO: Voir ou est-ce que ce truc est utilisé
    override def expand(expr: Expr): Expr = ??? /*expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }*/

    // TODO: Peut-on supposer que expr a été simplifié?
    override def implies(expr: Expr): Boolean = ??? // conditions contains expr
  }

  object Env extends PathProvider[Env] {
//    def empty = new Env(Set(), Map())
    def empty: Env = Env()
  }

  override def initEnv = Env.empty

  // TODO: Les local mutable state devront etre groupe dans un ThreadLocal!...

  // TODO: Le gag: comment repr. un lambda? Car la sol. naive semble fausse!!!
  // TODO: Pour les "unknown", on pourra utiliser un label unique (avec un id qu'on incrément à chaque fois)
  enum Label {
    case Var(v: Variable)
    case Tuple
    case ADT(id: Identifier, tps: Seq[Type])
    case FnInvoc(id: Identifier, tps: Seq[Type])

    case Or
    case Not

    case Equals
    case LessThan
    case GreaterThan
    case LessEquals
    case GreaterEquals

    case ArithOp(kind: ArithKind)
    case Lit[T](lit: Literal[T])

    case TupleSelect(index: Int)

    case FiniteSet(base: Type)
    // TODO: SetOps

    // TODO: Bag, etc.

    case FiniteArray(base: Type)
    // TODO: Comme args, il y a elems.values ++ Seq(default, size)
    //  On utilise indices pour reconstruire elems
    case LargeArray(elemIndices: Seq[Int], base: Type)
    case ArraySelect
    case ArrayUpdated
    case ArrayLength

    // TODO: le reste...

    // TODO: En gros, quand on sait pas, on incrémente un counter (label "unique" (pour exactement la meme expr, on obtient le meme label), pas de risque de faire n'importe quoi)
    case Unknown(id: Int)
  }

  enum ArithKind(commutative: Boolean) {
    case UMinus extends ArithKind(false)
    case Plus extends ArithKind(true)
    case Minus extends ArithKind(false)
    case Times extends ArithKind(true)
    case Division extends ArithKind(false)
    case Remainder extends ArithKind(false)
    case Modulo extends ArithKind(false)

    case BVNot extends ArithKind(false)
    case BVAnd extends ArithKind(true)
    case BVOr extends ArithKind(true)
    case BVXor extends ArithKind(true)
    case BVShiftLeft extends ArithKind(false)
    case BVAShiftRight extends ArithKind(false)
    case BVLShiftRight extends ArithKind(false)

    case BVNarrowingCast(newType: BVType) extends ArithKind(false)
    case BVWideningCast(newType: BVType) extends ArithKind(false)

    case BVUnsignedToSigned extends ArithKind(false)
    case BVSignedToUnsigned extends ArithKind(false)
  }

  opaque type Code = Int

  case class Signature(label: Label, children: Seq[Code])

  class OCBSL {
    import scala.collection.mutable

    private val codes = mutable.Map.empty[Expr, Code]
    private val sig2code = mutable.Map.empty[Signature, Code]
    private val code2sig = mutable.Map.empty[Code, Signature]

    // TODO: Voir si avoir un Map[Expr, Signature] est utile

    private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
    private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)

    private var unknownCounter = 0

    private val falseCode = updateCodesSig(falseSig)
    private val trueCode = updateCodesSig(trueSig)

    def codeOf(e: Expr): Code = codes.getOrElseUpdate(e, {
      val l = pDisj(e).sorted.distinct.filter(_ != falseCode)
      if (l.isEmpty) falseCode
      else if (l.size == 1) l.head
      else if (l.contains(trueCode) || checkForContradiction(l)) trueCode
      else {
        val sig = Signature(Label.Or, l)
        updateCodesSig(sig)
      }

      /*e match {
      case _ =>
        // TODO: Pas si vite pour le unknown!!! quid des subexprs?
        //  C'était justement pas le but de Unknown? En gros, tout est groupé dans un seul label (un "fat node" sans enfant)
        ???
      }*/
    })

    def checkForContradiction(disj: Seq[Code]): Boolean = {
      // TODO: Relativement different par rapport à l'impl.
      val disjSet = disj.toSet
      val (pos, neg) = disjSet.foldLeft((Set.empty[Code], Set.empty[Code])) {
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
              negDisj.forall(disjSet.contains)
            case _ => false
          }
        }
      }
    }

    def pDisj(e: Expr): Seq[Code] = {
      codes.get(e).map(code2sig) match {
        case Some(Signature(_, children)) => return children
        case None => ()
      }

      // TODO: Non, on ret une sig, et on update à la fin!
      // TODO: Est-ce la bonne chose à faire le unOr? Pk ne pas pat mat sur e?
      unOr(e) match {
        case Seq(Equals(e1, e2)) =>
          // TODO: Excepté pour c1 == c2, bcp de cas se ressemblent?
          val c1 = codeOf(e1)
          val c2 = codeOf(e2)
          if (c1 == c2) Seq(trueCode)
          else {
            val sig = Signature(Label.Equals, Seq(c1, c2))
            Seq(updateCodesSig(sig))
          }

        // TODO: Le reste...
        case Seq(Not(e)) =>
          ???
        case _ =>
          ???
      }
    }


    def updateCodesSig(sig: Signature): Code = {
      sig2code.getOrElseUpdate(sig, {
        val newCode: Code = sig2code.size
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
  }

}
