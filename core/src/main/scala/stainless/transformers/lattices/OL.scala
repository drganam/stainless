package stainless
package transformers
package lattices

import inox.solvers

trait OL extends Core {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable

  private val leqCache = mutable.Map.empty[(Env, Ctxs, Code, Code), Boolean]

  override final def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode) true
    else if (ctxs.allConds.isEmpty) false // car rhs != trueCode
    else {
      val lhsConj = conjunct(ctxs.allConds)
      latticesLeq(lhsConj, rhs)
    }
  }

  final def latticesLeq(lhs: Code, rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (lhs == rhs) true
    else leqCache.getOrElseUpdate((env, ctxs, lhs, rhs), (code2sig(lhs), code2sig(rhs)) match {
      case (BoolLitSig(b), _) => !b
      case (_, BoolLitSig(b)) => b
      case (_, OrSig(disjs, false)) =>
        disjs.forall(d => latticesLeq(lhs, negCodeOf(d)))
      case (OrSig(disjs, true), _) =>
        disjs.forall(latticesLeq(_, rhs))
      case (OrSig(disjs1, false), OrSig(disjs2, true)) =>
        disjs1.exists(c => latticesLeq(negCodeOf(c), rhs)) || disjs2.exists(c => latticesLeq(lhs, c))
      case (OrSig(disjs, false), _) =>
        disjs.exists(c => latticesLeq(negCodeOf(c), rhs))
      case (EqSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (EqSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (LtSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (GtSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case _ => false
    })
  }

  override final def doSimplifyDisjunction(disjs: Seq[Code])(using Env, Ctxs): Seq[Code] = {
    def rec(remaining: Seq[Code], accepted: Seq[Code]): Seq[Code] = remaining match {
      case Seq() => accepted
      case current +: rest =>
        val accept = (!remaining.exists(e => latticesLeq(current, e)) &&
          !accepted.exists(e => latticesLeq(current, e))) ||
          // TODO: Pureté imprécise! Il faudrait accumuler les disjs
          !codePurity(current).isPure
        rec(rest, if (accept) accepted :+ current else accepted)
    }

    rec(disjs, Seq.empty)
  }

  override def checkForContradiction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Option[Int] = {
    assert(disjs.size >= 2)
    val disjCode = codeOfSig(mkOr(disjs), BoolTy)
    val ix = {
      if (polarity) {
        val shadowChildren = disjs map negCodeOf
        shadowChildren.indexWhere(sc => latticesLeq(sc, disjCode))
      } else {
        val disjNegCode = negCodeOf(disjCode) // Car polarity inversé, donc c'est la négation qu'on passe
        disjs.indexWhere(c => latticesLeq(disjNegCode, c))
      }
    }
    if (ix < 0) None else Some(ix)
  }

  object NegSig {
    def unapply(sig: Signature): Option[Code] = sig match {
      case Signature(Label.Not, Seq(c)) => Some(c)
      case _ => None
    }
  }

  object VarSig {
    def unapply(sig: Signature): Option[(VarId, Boolean)] = sig match {
      case Signature(Label.Var(v), _) => Some((v, true))
      case Signature(Label.Not, Seq(c)) => code2sig(c) match {
        case Signature(Label.Var(v), _) => Some((v, false))
        case _ => None
      }
      case _ => None
    }
  }

  object OrSig {
    def unapply(sig: Signature): Option[(Seq[Code], Boolean)] = sig match {
      case Signature(Label.Or, disjs) => Some((disjs, true))
      case Signature(Label.Not, Seq(c)) => code2sig(c) match {
        case Signature(Label.Or, disjs) => Some((disjs, false))
        case _ => None
      }
      case _ => None
    }
  }

  object BoolLitSig {
    def unapply(sig: Signature): Option[Boolean] = sig match {
      case Signature(Label.Lit(BooleanLiteral(b)), _) => Some(b)
      case _ => None
    }
  }
}

object OL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OL
    new Impl(t, s, opts)
  }
}