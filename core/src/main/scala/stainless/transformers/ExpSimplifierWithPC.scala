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
//    case And // TODO: Nope
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

    // TODO: le reste...

    // TODO: En gros, quand on sait pas, on incrémente un counter (label "unique" (pour exactement la meme expr, on obtient le meme label), pas de risque de faire n'importe quoi)
    case Unknown(id: Int)
  }


  opaque type Code = Int

  case class Signature(label: Label, children: Seq[Code])

  class OCBSL {
    import scala.collection.mutable

    private val codes = mutable.Map.empty[Expr, Code]
    private val sig2code = mutable.Map.empty[Signature, Code]
    private val code2sig = mutable.Map.empty[Code, Signature]
    private val sizeCache = mutable.Map.empty[Expr, Int]

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
      // TODO: Relativement different par rapport à l'orig
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

    // TODO: Cela suppose que c'est une disjunction, mais c'est p-e pas le cas??? Ca peut etre une expr d'un autre type!!! (cf withBindings)
    def pDisj(e: Expr): Seq[Code] = {
//      computeSignature(e) match {
//        case Signature(Label.Not, Seq(c)) => pNeg(c)
//        case Signature(_, children) => children
//      }
      // TODO: Ok?
      computeSignature(e).children
    }

    // TODO: Signature de Not(child)
    def pNeg(child: Expr): Signature = {
      codes.get(child) match {
        case Some(c) => return pNegNormal(c)
        case None => ()
      }

      // TODO: Où devrait-on mettre le caching? C'est appelé par computeSignature donc ça devrait faire l'affaire non?

      child match {
        case Not(e) => computeSignature(e) // TODO: Orig fait pDisj, mais pDisj et un computeSignature pour nous (du moins, pour le moment)
        case or @ Or(_) =>
          val ors0 = unOr(or)
          // Note: ors cannot be empty (by Or `require`)
          val ors1 = ors0.sortBy(sizeOf)
          // TODO: Ici, on fait un filter..distinct.sorted, ce que l'orig ne fait pas vraiment?
          val r = ors1.tail.flatMap(pDisj)
            .filter(_ != falseCode)
            .distinct.sorted
          if (r.isEmpty) pNeg(ors1.head) // TODO: Caching?
          else {
            // TODO: Ok?
            val s = (pDisj(ors1.head) ++ r)
              .filter(_ != falseCode)
              .distinct.sorted
            if (s.contains(trueCode) || checkForContradiction(s)) falseCode
            else if (s.size == 1) pNegNormal(s.head) // TODO: Ok?
            else {
              val orCode = updateCodesSig(Signature(Label.Or, s))
              Signature(Label.Not, orCode)
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

      /*
      // TODO: Apparemment, ce n'est pas le truc à faire avec computeSignature?
      //  L'orig check d'abord si normal form deja compute. Si oui, fait un pNegNormal
      computeSignature(child) match {
        case Signature(Label.Lit(BooleanLiteral(b)), Seq()) =>
          Signature(Label.Lit(BooleanLiteral(!b)), Seq.empty)
        case Signature(Label.Not, Seq(c)) =>
          // TODO: Ok?
          code2sig(c)
        case Signature(Label.Or, Seq()) =>
          // TODO: Comme dans l'orig, mais est-ce "vraiment vrai"?
          trueSig
        case Signature(Label.Or, cs) =>


          ???
        case sig =>
          // TODO: Ok?
          Signature(Label.Not, Seq(sig2code(sig)))
      }
      */
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
    def computeSignature(e: Expr): Signature = {
      codes.get(e).map(code2sig) match {
        case Some(sig) => return sig
        case None => ()
      }

      // TODO: Check label (pour voir s'il n'y a pas d'erreur de copié/collé)
      val sig = e match {
        // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
        case and @ And(_) =>
          val ands = unAnd(and)
//          Signature(Label.And, ands.map(codeOf).sorted) // TODO: Nope
//          computeSignature(Neg(Or(ands.map(Neg)))) // TODO: codeOf ou computeSignature?
          code2sig(codeOf(Not(Or(ands.map(Not.apply)))))
        case or @ Or(_) =>
          val ors = unOr(or)
          Signature(Label.Or, ors.map(codeOf).sorted) // TODO: checkForContradiction?
        case Not(e) =>
          pNeg(e)
//          // TODO: Non!!! C'est pNeg!!!
//          Signature(Label.Not, Seq(codeOf(e)))
        case Implies(e1, e2) =>
//          computeSignature(Or(Not(e1), e2)) // TODO: codeOf ou computeSignature?
          code2sig(codeOf(Or(Not(e1), e2)))

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

        /*
        case Equals(e1, e2) =>
          Signature(Label.Equals, Seq(codeOf(e1), codeOf(e2)).sorted)
        case LessThan(e1, e2) =>
          Signature(Label.LessThan, Seq(codeOf(e1), codeOf(e2)))
        case GreaterThan(e1, e2) =>
          Signature(Label.GreaterThan, Seq(codeOf(e1), codeOf(e2)))
        case LessEquals(e1, e2) =>
          Signature(Label.LessEquals, Seq(codeOf(e1), codeOf(e2)))
        case GreaterEquals(e1, e2) =>
          Signature(Label.GreaterEquals, Seq(codeOf(e1), codeOf(e2)))
        */

        // TODO: Ne pourrait-on pas envisager certains simplif. ici?
        case UMinus(e) =>
          Signature(Label.UMinus, Seq(codeOf(e)))
        case Plus(e1, e2) =>
          Signature(Label.Plus, Seq(codeOf(e1), codeOf(e2)).sorted)
        case Minus(e1, e2) =>
          Signature(Label.Minus, Seq(codeOf(e1), codeOf(e2)))
        case Times(e1, e2) =>
          Signature(Label.Times, Seq(codeOf(e1), codeOf(e2)).sorted)
        case Division(e1, e2) =>
          Signature(Label.Division, Seq(codeOf(e1), codeOf(e2)))
        case Remainder(e1, e2) =>
          Signature(Label.Remainder, Seq(codeOf(e1), codeOf(e2)))
        case Modulo(e1, e2) =>
          Signature(Label.Modulo, Seq(codeOf(e1), codeOf(e2)))

        case BVNot(e) =>
          Signature(Label.BVNot, Seq(codeOf(e)))
        case BVAnd(e1, e2) =>
          Signature(Label.BVAnd, Seq(codeOf(e1), codeOf(e2)).sorted)
        case BVOr(e1, e2) =>
          Signature(Label.BVOr, Seq(codeOf(e1), codeOf(e2)).sorted)
        case BVXor(e1, e2) =>
          Signature(Label.BVXor, Seq(codeOf(e1), codeOf(e2)).sorted)
        case BVShiftLeft(e1, e2) =>
          Signature(Label.BVShiftLeft, Seq(codeOf(e1), codeOf(e2)))
        case BVAShiftRight(e1, e2) =>
          Signature(Label.BVAShiftRight, Seq(codeOf(e1), codeOf(e2)))
        case BVLShiftRight(e1, e2) =>
          Signature(Label.BVLShiftRight, Seq(codeOf(e1), codeOf(e2)))

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

        case BooleanLiteral(b) =>
          if (b) trueSig else falseSig // TODO: Semble redondant avec le case en dessous?

        case l: Literal[_] =>
          Signature(Label.Lit(l), Seq.empty)

        case _ =>
          println(s"Generated an 'unknown' for $e (with id $unknownCounter)")
          val sig = Signature(Label.Unknown(unknownCounter), Seq.empty)
          unknownCounter += 1
          sig
      }

      updateCodesSig(sig)
      sig
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
