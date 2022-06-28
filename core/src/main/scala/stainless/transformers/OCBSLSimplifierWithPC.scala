package stainless
package transformers

trait OCBSLSimplifierWithPC extends Transformer with stainless.transformers.SimplifierWithPC { self =>
  val trees: ast.Trees
  import trees._
  import symbols.{given, _}

//  override val pp: PathProvider[Env] = Env

  private val ocbslTL = {
    class OCBSLImpl(override val trees: self.trees.type, override val symbols: self.symbols.type)
      extends ocbsl.OCBSL(trees, symbols, opts)
    ThreadLocal.withInitial(() => new OCBSLImpl(trees, symbols))
  }

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    println("")
    println("SIMPLIFY:")
    println(e)
    println("PATH: " + path)
//    assert(path.bound.isEmpty) // TODO: Pr le moment

    val oc = ocbslTL.get()
    val code = oc.codeOf(e)(using oc.OEnv.empty)
    val res0 = oc.uncodeOf(code)(using oc.RevEnv.empty)
    println(s"I haz $path")
    println(s"I haz ${res0.holed.holes}")
//    val tayst = res0.holed.expr(Map(2 -> Variable.fresh("AAAAAA", Untyped)))
//    println(tayst)
    assert(res0.holed.holes.isEmpty, s"Result has holes: ${res0.holed.holes.toSeq.sorted}") // TODO: Ce n'est p-e pas vrai en raison de path!!! (-> il suffira de mettre des vds dummy)
    val res = res0.holed.expr(Map.empty).copiedFrom(e)
    (res, oc.codePurity(code).isPure)
  }
/*
  case class Env(conditions: Set[Code],
                 exprSubst: Map[Variable, Expr],
                 exprCode: Map[Variable, Code],
                 // Note: Order is important (hence Seq)
                 bound: Seq[ValDef]) extends PathLike[Env] with SolvingPath {
    // TODO: On pourra supposer que le binding a été simplifié avant
    override def withBinding(p: (ValDef, Expr)): Env = ??? /*p match {
      // TODO: Qq binding ajouté
      // TODO: Pk n'ajoute-t-on pas tous les bdgs?
      //  ~> p-e parce que le Let case n'exploite pas ces infos?
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda | _: FiniteArray | _: LargeArray)) =>
        // TODO: Quid purity???
        val c = ocbsl.codeOf(expr)(using mkSubst)
        Env(conditions, exprSubst + (vd.toVariable -> expr), exprCode + (vd.toVariable -> c), bound)
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) {
          val c = ocbsl.codeOf(exp)(using mkSubst)
          Env(conditions, exprSubst + (vd.toVariable -> exp), exprCode + (vd.toVariable -> c), bound)
        } else this
      case _ => this
    }*/

    override def withBound(vd: ValDef): Env = ??? // Env(conditions, exprSubst, exprCode, bound :+ vd)

    // TODO: On pourra supposer que cond a été simplifié avant
    override def withCond(cond: Expr): Env = ??? /*{
      // TODO: Et si cond est impure???
      val codeCond = ocbsl.codeOf(cond)(using mkSubst)
      Env(conditions + codeCond, exprSubst, exprCode, bound)
    }*/

    override def negate: Env = ??? /*{
      given Subst = mkSubst
      Env(Set(ocbsl.negatedConjunction(conditions)), exprSubst, exprCode, bound)
    }*/

    override def merge(that: Env): Env = ??? // Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst, exprCode ++ that.exprCode, bound ++ that.bound)

    // TODO: Voir ou est-ce que ce truc est utilisé
    override def expand(expr: Expr): Expr = ??? /*expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }*/

    // TODO: Peut-on supposer que expr a été simplifié??? Il semblerait que non!!!!
    // TODO: Quid purity??? p.ex. size(l) ==> size(l) se fait transformer en true!!!!
    override def implies(expr: Expr): Boolean = {
      ???
//       if (expr.getType != BooleanType()) false
//       else {
//         given Subst = mkSubst
//         // TODO: Purity????
//         ocbsl.implied(ocbsl.codeOf(expr))
//       }
    }

//    def mkSubst: Subst = {
//      // TODO: Ok?
//      Subst(conditions, free = exprCode, bound = Map.empty, 0, letDef = Map.empty)
//        .withOpenBounds(bound)
//    }
  }

  object Env extends PathProvider[Env] {
    def empty: Env = Env(Set.empty, Map.empty, Map.empty, Seq.empty)
  }

  override def initEnv: Env = Env.empty*/
}
