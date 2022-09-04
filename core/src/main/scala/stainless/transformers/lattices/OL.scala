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

  private val leqCache = mutable.Map.empty[(Code, Code), Boolean]

  override final def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode) true
    else if (ctxs.allConds.isEmpty) false // car rhs != trueCode
    else {
      val lhsConj = conjunct(ctxs.allConds)
      latticesLeq(lhsConj, rhs)
    }
  }

  final def latticesLeq(lhs: Code, rhs: Code): Boolean = {
    if (lhs == rhs) true
    else leqCache.getOrElseUpdate((lhs, rhs), (code2sig(lhs), code2sig(rhs)) match {
      case (BoolLitSig(b), _) => !b
      case (_, BoolLitSig(b)) => b

      case (OrSig(disjs1, false), OrSig(disjs2, true)) =>
        disjs1.exists(c => latticesLeq(negCodeOf(c), rhs)) || disjs2.exists(latticesLeq(lhs, _))

      case (_, OrSig(disjs, false)) =>
        disjs.forall(d => latticesLeq(lhs, negCodeOf(d)))

      case (OrSig(disjs, true), _) =>
        disjs.forall(latticesLeq(_, rhs))

      case (_, OrSig(disjs, true)) =>
        disjs.exists(latticesLeq(lhs, _))

      case (OrSig(disjs, false), _) =>
        disjs.exists(c => latticesLeq(negCodeOf(c), rhs))

      case (EqSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (EqSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (LtSig(lhs1, rhs1), LeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2
      case (GtSig(lhs1, rhs1), GeqSig(lhs2, rhs2)) => lhs1 == lhs2 && rhs1 == rhs2

      case _ => false
    })
  }

  override final def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Seq[Code] = {
    if (disjs.size <= 1) return disjs

    val nonSimp = {
      val or = codeOfDisjs(disjs)
      if (polarity) or
      else codeOfSig(mkNot(or), BoolTy)
    }

    def treatChild(phiKs: Code): Seq[Code] = code2sig(phiKs) match {
      case OrSig(psiJs, true) => psiJs
      case OrSig(psiJs, false) =>
        if (polarity) {
          findMap(psiJs) { psiJ =>
            val neg = negCodeOf(psiJ)
            if (latticesLeq(neg, nonSimp)) Some(treatChild(neg))
            else None
          }.getOrElse(Seq(phiKs))
        } else {
          findMap(psiJs) { psiJ =>
            if (latticesLeq(nonSimp, psiJ)) Some(treatChild(negCodeOf(psiJ)))
            else None
          }.getOrElse(Seq(phiKs))
        }
      case _ => Seq(phiKs)
    }

    def rec(remaining: Seq[Code], accepted: Seq[Code]): Seq[Code] = remaining match {
      case Seq() => accepted
      case current +: remaining =>
        if (remaining.size + accepted.size == 0) Seq(current)
        else {
          val all = codeOfDisjs(remaining ++ accepted)
          val accept = !latticesLeq(current, all) ||
            // TODO: Pureté imprécise! Il faudrait accumuler les disjs
            !codePurity(current).isPure
          rec(remaining, if (accept) accepted :+ current else accepted)
        }
    }

    val disjs2 = disjs.flatMap(treatChild)
    rec(disjs2, Seq.empty)
  }

  override def checkForContradiction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Option[Int] = {
    assert(disjs.size >= 2)
    val disjCode = codeOfSig(mkOr(disjs), BoolTy)
    val ix = {
      if (polarity) {
        val shadowChildren = disjs map negCodeOf
        shadowChildren.indexWhere(latticesLeq(_, disjCode))
      } else {
        val disjNegCode = negCodeOf(disjCode) // Car polarity inversé, donc c'est la négation qu'on passe
        disjs.indexWhere(latticesLeq(disjNegCode, _))
      }
    }
    if (ix < 0) None else Some(ix)
  }

  private def codeOfDisjs(d: Seq[Code]): Code = {
    assert(d.nonEmpty)
    if (d.size == 1) d.head else codeOfSig(mkOr(d), BoolTy)
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
}

object OL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OL
    new Impl(t, s, opts)
  }
}