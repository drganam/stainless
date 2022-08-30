package stainless
package transformers
package lattices

import inox.solvers

trait OCBSL extends Common {
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

  override final def simplifiedDisjunction(disj0: Seq[Code], polarity: Boolean)(using Env, Ctxs): Code = {
    assert(disj0.forall(c => codeTpe(c) == BoolTy))
    val disj = unOrCodes(disj0)
    val disjs1 = disj.filter(_ != falseCode).distinct
    val simp = {
      if (disjs1.isEmpty) falseCode
      else if (disjs1.size == 1) disjs1.head
      else {
        val lastKeptIx = Some(disjs1.indexOf(trueCode)).filter(_ >= 0)
          .orElse(checkForContradiction(disjs1))
          .getOrElse(disjs1.length - 1)

        if (lastKeptIx == disjs1.length - 1 && disjs1.last != trueCode) {
          // Nothing simplified, so just make the disjunction and return
          // TODO: Sort if "truly pure" and not pure due to binding!
          // val disjs2 = if (purities.forall(_.isPure)) disjs1.sorted else disjs1
          codeOfSig(mkOr(disjs1), BoolTy)
        } else {
          // Due to short-circuiting, once the disjunction evaluates to true, the remaining disjuncts won't ever be evaluated
          // so it is safe to drop them -- including impure expressions.
          val disjs2 = disjs1.take(lastKeptIx + 1)
          val disjs2Purities = disjs2.map(codePurity)
          if (disjs2Purities.forall(_.isPure)) trueCode
          else {
            // Add a trailing `true` if not already present (because the disjunction will evaluate to true,
            // but due to the presence of impure expressions, we are not allowed to simplify the whole expr to true
            val disjs3 = if (disjs2.contains(trueCode)) disjs2 else disjs2 :+ trueCode
            codeOfSig(mkOr(disjs3), BoolTy)
          }
        }
      }
    }
    if (polarity) simp else negCodeOf(simp)
  }

  final def checkForContradiction(disjs0: Seq[Code]): Option[Int] = {
    // Convert a >= b and a > b to !(a < b) and !(a <= b) respectively.
    // This will ease the work of for the rest of the fn.
    // Assumes that disjs is normalized (i.e. we have `a` instead of !!a, a <= b instead of !(a > b) etc.)
    // so in some sense we are denormalizing parts of the given disjs.
    // If disjs is not normalized, denormalize may return expressions such as !!(a > b),
    // which may cause a contradiction to be missed.
    def denormalize(disjs: Seq[Code]): Seq[Code] = {
      disjs.map { c =>
        code2sig(c) match {
          case Signature(Label.GreaterEquals, Seq(a, b)) =>
            val lt = codeOfSig(mkLessThan(a, b), BoolTy)
            codeOfSig(mkNot(lt), BoolTy)
          case Signature(Label.GreaterThan, Seq(a, b)) =>
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