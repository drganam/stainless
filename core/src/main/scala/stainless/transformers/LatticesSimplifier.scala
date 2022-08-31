package stainless
package transformers

import inox.solvers

import java.util.concurrent.atomic.AtomicInteger

// Wrapper that sets up a thread-local ocbsl algo instance
trait LatticesSimplifier { self =>
  import LatticesSimplifier._
  val trees: ast.Trees
  val symbols: trees.Symbols
  val opts: solvers.PurityOptions
  val algo: UnderlyingAlgo

  import trees._
  import symbols.{given, _}

  private val coreTL: ThreadLocal[lattices.Core{val trees: self.trees.type; val symbols: self.symbols.type}] =
    ThreadLocal.withInitial(() => algo match {
      case UnderlyingAlgo.OCBSL => lattices.OCBSL(trees, symbols, opts)
      case UnderlyingAlgo.OL => lattices.OL(trees, symbols, opts)
    })

  private val vcNum: AtomicInteger = new AtomicInteger(0)

  val poi = 17

  def simplify(e: Expr): Expr = {
//    if (vcNum.get() < poi) {
//      println("TAKING THE EASY ROUTE #1")
//      println("TAKING THE EASY ROUTE #2")
//      println("TAKING THE EASY ROUTE #3")
//      vcNum.incrementAndGet()
//      return BooleanLiteral(true)
//    } else if (vcNum.get() > poi) ???
//    println("")
//    println("SIMPLIFY:")
//    println(e)
    val core = coreTL.get()
    given core.Env = core.Env.empty
    given core.Ctxs = core.Ctxs.empty
    given core.LetValSubst = core.LetValSubst.empty

    val resE = core.codeOfExpr(e)
    val codeE = resE.selfPlugged(core.Ctxs.empty)._2
    val res = core.uncodeOf(codeE)(using core.RevEnv.empty).expr.copiedFrom(e)
    vcNum.incrementAndGet()
    res
  }
}
object LatticesSimplifier {

  enum UnderlyingAlgo {
    case OCBSL
    case OL
  }

  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions, algo: UnderlyingAlgo): LatticesSimplifier{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions, override val algo: UnderlyingAlgo) extends LatticesSimplifier
    new Impl(t, s, opts, algo)
  }
}