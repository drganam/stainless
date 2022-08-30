package stainless
package transformers
package lattices

import inox.solvers

trait OCBSL extends Core {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._

  override final def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode) true
    else if (ctxs.allConds.isEmpty) false // car rhs != trueCode
    else {
      // a ==> b === a && b = a
      val lhsConj = conjunct(ctxs.allConds)
      val rhsLhsConj = conjunct(Seq(lhsConj, rhs))
      rhsLhsConj == lhsConj
    }
  }

  override final def doSimplifyDisjunction(disj0: Seq[Code])(using Env, Ctxs): Seq[Code] = disj0

  override final def checkForContradiction(disjs0: Seq[Code], polarityUnused: Boolean)(using Env, Ctxs): Option[Int] = {
    // Convert a >= b and a > b to !(a < b) and !(a <= b) respectively.
    // This will ease the work of for the rest of the fn.
    // Assumes that disjs is normalized (i.e. we have `a` instead of !!a, a <= b instead of !(a > b) etc.)
    // so in some sense we are denormalizing parts of the given disjs.
    // If disjs is not normalized, denormalize may return expressions such as !!(a > b),
    // which may cause a contradiction to be missed.
    def denormalize(disjs: Seq[Code]): Seq[Code] = {
      disjs.map { c =>
        code2sig(c) match {
          case GeqSig(a, b) =>
            val lt = codeOfSig(mkLessThan(a, b), BoolTy)
            codeOfSig(mkNot(lt), BoolTy)
          case GtSig(a, b) =>
            val leq = codeOfSig(mkLessEquals(a, b), BoolTy)
            codeOfSig(mkNot(leq), BoolTy)
          case _ => c
        }
      }
    }

    val disjs = denormalize(disjs0)

    def firstTry(i: Int, pos: Set[Code], neg: Set[Code]): Either[(Set[Code], Set[Code]), Int] = {
      if (i == disjs.length) Left((pos, neg))
      else {
        val c = disjs.head
        code2sig(c) match {
          case Signature(Label.Not, Seq(cc)) =>
            if (pos(cc)) Right(i)
            else firstTry(i + 1, pos, neg + cc)
          case _ =>
            if (neg(c)) Right(i)
            else firstTry(i + 1, pos + c, neg)
        }
      }
    }

    firstTry(0, Set.empty, Set.empty) match {
      case Right(ix) => Some(ix)
      case Left((_, neg)) =>
        val found = neg.exists { negC =>
          code2sig(negC) match {
            case Signature(Label.Or, negDisj) =>
              // TODO: Est-ce vrai? Quid si un meme code apparait dans un truc negatif?
              denormalize(negDisj).forall(disjs.contains)
            case _ => false
          }
        }
        if (found) Some(disjs.length - 1) else None
    }
  }
}

object OCBSL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OCBSL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OCBSL
    new Impl(t, s, opts)
  }
}