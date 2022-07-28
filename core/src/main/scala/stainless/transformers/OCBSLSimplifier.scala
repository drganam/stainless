package stainless
package transformers

import inox.solvers

// Wrapper that sets up a thread-local ocbsl algo instance
trait OCBSLSimplifier { self =>
  val trees: ast.Trees
  val symbols: trees.Symbols
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}

  private val ocbslTL: ThreadLocal[ocbsl.OCBSL{val trees: self.trees.type; val symbols: self.symbols.type}] =
    ThreadLocal.withInitial(() => ocbsl.OCBSL(trees, symbols, opts))

  private var vcNum: Int = 1

  def simplify(e: Expr): Expr = {
//    if (vcNum >= 10) {
//      ???
//    }
//    println("")
//    println("SIMPLIFY:")
//    println(e)
    val oc = ocbslTL.get()
    given oc.OEnv = oc.OEnv.empty
    given oc.Ctxs = oc.Ctxs.empty

    val resE = oc.codeOfExpr(e)
    val codeE = resE.selfPlugged(oc.Ctxs.empty)._2
    val res = oc.uncodeOf(codeE)(using oc.RevEnv.empty).expr.copiedFrom(e)
    vcNum += 1
    res
  }
}
object OCBSLSimplifier {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OCBSLSimplifier{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OCBSLSimplifier
    new Impl(t, s, opts)
  }
}