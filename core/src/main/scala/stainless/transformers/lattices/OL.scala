package stainless
package transformers
package lattices

import inox.solvers

trait OL extends Common {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable

  private val leqCache = mutable.Map.empty[(Code, Code), Boolean]

  override final def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode) true
    else if (ctxs.allConds.isEmpty) false // car rhs != trueCode
    else {
      val lhsConj = conjunct(ctxs.allConds)
      latticesLeq(lhsConj, rhs)
    }
  }

  // TODO: Unored?
  final def latticesLeq(lhs: Code, rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (lhs == rhs) true
    // TODO: Le cache
    else leqCache.getOrElseUpdate((lhs, rhs), (code2sig(lhs), code2sig(rhs)) match {
      case (BoolLitSig(b), _) => !b
      case (_, BoolLitSig(b)) => b
      case (VarSig(v1, polarity1), VarSig(v2, polarity2)) =>
        v1 == v2 && polarity1 == polarity2
      case (_, OrSig(disjs, false)) =>
        disjs.forall(d => latticesLeq(lhs, negCodeOf(d)))
      case (OrSig(disjs, true), _) =>
        disjs.forall(latticesLeq(_, rhs))
      case (OrSig(disjs, false), VarSig(_, _)) =>
        disjs.exists(c => latticesLeq(negCodeOf(c), rhs))
      case (OrSig(disjs1, false), OrSig(disjs2, true)) =>
        disjs1.exists(c => latticesLeq(negCodeOf(c), rhs)) || disjs2.exists(c => latticesLeq(lhs, c))
      // TODO: <= < >= > ==
      case _ => false
    })
  }

  override final def simplifiedDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Code = {
    val flattened = disjs.flatMap(c => code2sig(c) match {
      case OrSig(disjs2, true) => disjs2
      case _ => Seq(c)
    })

    def rec(remaining: Seq[Code], accepted: Seq[Code]): Seq[Code] = remaining match {
      case Seq() => accepted
      case current +: rest =>
        val accept = (!remaining.exists(e => latticesLeq(current, e)) &&
          !accepted.exists(e => latticesLeq(current, e))) ||
          !codePurity(current).isPure
        rec(rest, if (accept) accepted :+ current else accepted)
    }

    val accepted = rec(flattened, Seq.empty)
    accepted match {
      case Seq() => b2c(!polarity)
      case Seq(single) => if (polarity) single else negCodeOf(single)
      case _ =>
        val disjs2 = codeOfSig(mkOr(accepted), BoolTy)
        ???
//        if (checkForContradiction2(disjs2, accepted)) b2c(polarity)
//        else if (polarity) disjs2
//        else negCodeOf(disjs2)
    }
  }

  final def checkForContradiction2(disjCode: Code, disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Boolean = {
    assert(code2sig(disjCode) == Signature(Label.Or, disjs))
    if (polarity) {
      val shadowChildren = disjs map negCodeOf
      shadowChildren.exists(sc => latticesLeq(sc, disjCode))
    } else {
      disjs.exists(c => latticesLeq(disjCode, c))
    }
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