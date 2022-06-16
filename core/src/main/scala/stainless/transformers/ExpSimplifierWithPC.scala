package stainless
package transformers

trait ExpSimplifierWithPC extends Transformer with stainless.transformers.SimplifierWithPC {
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

  override val pp: PathProvider[Env] = Env

  private val ocbslTL = ThreadLocal.withInitial(() => new OCBSL)
  private val ocbsl = ocbslTL.get() // TODO: Est-ce que cela obtient la copie local ou cela fait n'importe quoi???

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    val (re, pr) = e match {
      case Implies(l, r) =>
        val (rl, pl) = simplify(l, path)
        rl match {
          case BooleanLiteral(false) if pl => return (BooleanLiteral(true).copiedFrom(e), true) // TODO: Legal?
          case _ => ()
        }
        val newPath = if (pl) path withCond rl else path
        val (rr, pr) = simplify(r, newPath) // TODO: Legal?
        if (pl && pr) (implies(rl, rr).copiedFrom(e), true)
        else (Implies(rl, rr).copiedFrom(e), false)
//        // TODO: Utiliser env! Ou est-ce déjà le cas?
//        rr match {
//          case BooleanLiteral(_) /*if pl*/ =>
//            (rr, pr) // TODO: Legal?
//          case _ => (implies(rl, rr).copiedFrom(e), pl && pr)
//        }
      // TODO: Ce truc semble inutile? Ou bien?
      //    case e if e.getType == BooleanType() =>
      //      val (re, pe) = super.simplify(e, path)
      //      if (pe) (ocbsl.simplify(re), true)
      //      else (re, false)
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

  private val fns = scala.collection.mutable.Map.empty[Identifier, Boolean]

//  def containsImpureExpr(expr: Expr): Boolean = exprOps.exists {
//    case (_: Assume) | (_: Choose) | (_: Application) |
//         (_: Division) | (_: Remainder) | (_: Modulo) | (_: ADTSelector) |
//         (_: Decreases) | (_: Require) | (_: Ensuring) | (_: Assert) => true
//    case FunctionInvocation(id, _, _) =>
//      fns.getOrElseUpdate(id, )
//      // Note: args already checked recursively
//      containsImpureExpr(getFunction(id).fullBody)
//    case adt: ADT => adt.getConstructor.sort.definition.hasInvariant
//    case _ => false
//  } (expr)

  case class Env(conditions: Set[Code], exprSubst: Map[Variable, Expr], exprCode: Map[Variable, Code]) extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = p match {
      // TODO: Qq binding ajouté
      // TODO: Pk n'ajoute-t-on pas tous les bdgs?
      //  ~> p-e parce que le Let case n'exploite pas ces infos?
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda | _: FiniteArray | _: LargeArray)) =>
        val c = ocbsl.codeOf(expr)(using exprCode)
        Env(conditions, exprSubst + (vd.toVariable -> expr), exprCode + (vd.toVariable -> c))
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) {
          val c = ocbsl.codeOf(exp)(using exprCode)
          Env(conditions, exprSubst + (vd.toVariable -> exp), exprCode + (vd.toVariable -> c))
        } else this
      case _ => this
    }

    /*p match {
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
    // TODO: Et si cond est impure???
    override def withCond(cond: Expr): Env = {
      val codeCond = ocbsl.codeOf(cond)(using exprCode)
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
    // TODO: Peut-on supposer que expr a été simplifié??? Il semblerait que non!!!!
    // TODO: Peut-on supposer que expr a été simplifié??? Il semblerait que non!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    override def implies(expr: Expr): Boolean = {
//      if (containsImpureExpr(expr)) {
//        println(s"Note: $expr en implication rejeté")
//        return false
//      }
//      println("============================")
//      println("A-t-on cette implication?")
//      println(s"     $conditions    ==>    $expr")
      // TODO: On pourrait utiliser les bindings non?
      val r = ocbsl.implies(conditions, ocbsl.codeOf(expr)(using exprCode))
//      println(s"     La réponse est $r")
//      println("============================")
      r
//      false
    }
  }

  object Env extends PathProvider[Env] {
    def empty: Env = Env(Set.empty, Map.empty, Map.empty)
  }

  override def initEnv: Env = Env.empty

  // TODO: Le gag: comment repr. un lambda? Car la sol. naive semble fausse!!!
  enum Label {
    case Var(v: Variable)
    case Tuple
    case ADT(id: Identifier, tps: Seq[Type])
    case ADTSelector(selector: Identifier)
    case FunctionInvocation(id: Identifier, tps: Seq[Type])
    case Annotated(flags: Seq[Flag])

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

    // TODO: le reste...

    // TODO: En gros, quand on sait pas, on incrémente un counter (label "unique" (pour exactement la meme expr, on obtient le meme label), pas de risque de faire n'importe quoi)
    case Unknown(underlying: Expr) // TODO: Ou bien garde-t-on le compteur
  }


  opaque type Code = Int

  case class Signature(label: Label, children: Seq[Code])

  private class OCBSL {
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

    // TODO: Au lieu de balader cette map, pourrait-on envisager de la mettre comme un field?
    //    ~> non! les let bindings sont "temporaire"!!!
    def codeOf(e: Expr)(using Map[Variable, Code]): Code = codes.getOrElseUpdate(e, {
      // TODO: ok?
      val pDisjRes = pDisj(e)
      val res = simplifiedDisjunction(pDisjRes.toSet)
      res
      /*
      val l = pDisj(e).sorted.distinct.filter(_ != falseCode)
      if (l.isEmpty) falseCode
      else if (l.size == 1) l.head
      else if (l.contains(trueCode) || checkForContradiction(l)) trueCode
      else {
        val sig = Signature(Label.Or, l)
        updateCodesSig(sig)
      }
      */
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
      else simplifiedDisjunction(lhs + rhs) == rhs
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
    def pDisj(e: Expr)(using Map[Variable, Code]): Seq[Code] = {
      computeSignature(e) match {
        case Signature(Label.Or, children) => children
        case sig => Seq(updateCodesSig(sig))
      }
    }

    // TODO: Signature de Not(child)
    def pNeg(child: Expr)(using Map[Variable, Code]): Signature = {
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
    def computeSignature(e: Expr)(using subst: Map[Variable, Code]): Signature = {
      codes.get(e).map(code2sig) match {
        case Some(sig) => return sig
        case None => ()
      }

      // TODO: Check label (pour voir s'il n'y a pas d'erreur de copié/collé)
      val sig = e match {
        case v: Variable =>
          subst.get(v).map(code2sig)
            .getOrElse(Signature(Label.Var(v), Seq.empty))
        case Tuple(args) =>
          Signature(Label.Tuple, args.map(codeOf))
        case ADT(id, tps, args) =>
          Signature(Label.ADT(id, tps), args.map(codeOf))
        case ADTSelector(e, selector) =>
          Signature(Label.ADTSelector(selector), Seq(codeOf(e)))
        case FunctionInvocation(id, tps, args) =>
          Signature(Label.FunctionInvocation(id, tps), args.map(codeOf))

        // TODO: Problématique, car si vd est pas utilisé, on peut drop des constructions "impures"
//        case Let(vd, e, body) =>
//          val cE = codeOf(e)
//          val cB = codeOf(body)(using subst + (vd.toVariable -> cE))
//          code2sig(cB)

        // TODO: If, "is", Application, lambda

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

//        case BooleanLiteral(b) =>
//          if (b) trueSig else falseSig // TODO: Semble redondant avec le case en dessous?

        case l: Literal[_] =>
          Signature(Label.Lit(l), Seq.empty)

        case _ =>
          // TODO: Ou bien garde-t-on le compteur?
//          println(s"Generated an 'unknown' for $e")
          Signature(Label.Unknown(e), Seq.empty)
          /*
          println(s"Generated an 'unknown' for $e (with id $unknownCounter)")
          val sig = Signature(Label.Unknown(unknownCounter), Seq.empty)
          unknownCounter += 1
          sig
          */
      }

      val leCodeeee = updateCodesSig(sig)
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
