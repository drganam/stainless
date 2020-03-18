/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package trace

trait Trace extends CachingPhase with SimpleFunctions with IdentitySorts { self =>
  val s: Trees
  val t: termination.Trees
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({(fd, symbols) => 
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id)
        .flatMap(id => symbols.lookupFunction(id))
    )
  })

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] object identity extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }
                    
  override protected def extractFunction(symbols: Symbols, fd: FunDef): t.FunDef = {
    import symbols._
    var v3 = fd.fullBody
    val result: FunDef = if(fd.flags.contains(TraceInduct)) {
                           fd.fullBody match {
                             case Ensuring(body, pred) => {
                               body match {
                                 case Equals(f1, f2) => {
                                   val proof: Expr = prove(symbols, fd, f1) match {
                                                       case Some(e) => e
                                                       case None => prove(symbols, fd, f2) match {
                                                         case Some(e) => e
                                                         case None => fd.fullBody
                                                       }
                                                     }
                                   fd.copy(fd.id, fd.tparams, fd.params, fd.returnType, Ensuring(And(proof, body), pred), fd.flags)
                                 }
                                 case _ => fd
                               }
                             }
                             case _ => fd
                           }
                         }
                         else fd
                         
    if(result.fullBody != fd.fullBody) System.out.println(result.fullBody)
    
    identity.transform(result.copy(flags = result.flags filterNot (f => f == TraceInduct)))
  }
  
  private def prove(symbols: Symbols, fd: FunDef, fcall: Expr): Option[Expr] = {
    fcall match {
      case FunctionInvocation(id,t,a) => {
        funInduct(symbols, fd, symbols.functions.filter(elem => elem._2.id == id).head._2)
      }
      case _ => None
    }
  }

  private def funInduct(symbols: Symbols, fd: FunDef, fInduct: FunDef): Option[Expr] = {
    import symbols._

    System.out.println(fInduct.id)
    inductPattern(symbols, fInduct.fullBody)
    //Some(inductPattern(fInduct.fullBody))

    None
  }

  private def inductPattern(symbols: Symbols, expr: Expr): Expr = {
    import symbols._
    
    expr match {
      case MatchExpr(scr, cases) => {
        inductPattern(symbols, matchToIfThenElse(expr))
      }
      case IfExpr(cond, thenn, elze) => {
        System.out.println("if")
        System.out.println("before")
        System.out.println(expr)
        System.out.println("after")
        System.out.println(IfExpr(inductPattern(symbols, cond), inductPattern(symbols, thenn), inductPattern(symbols, elze)).copiedFrom(expr))
        IfExpr(inductPattern(symbols, cond), inductPattern(symbols, thenn), inductPattern(symbols, elze)).copiedFrom(expr)
      }
      case Operator(args, op) => {
        System.out.println("op")
        expr
      }
      case Let(i, v, b) => {
        System.out.println("let")
        expr
      }
      case FunctionInvocation(n, t, p) => {
        System.out.println("functioninv")
        expr
      }
      case _ => {
        System.out.println("default")
        expr
      }
    }
  }

  private def containsRecursiveCalls(expr: Expr, fd: FunDef) = {
    exprOps.functionCallsOf(expr).map((elem: FunctionInvocation) => elem.id).contains(fd.id)
  }
  
  def replaceSymbols(expr: Expr, from: Seq[Variable], to: Seq[Variable], fromf: FunDef, tof: FunDef): Option[Expr] = {
    val errorVariable = Variable.fresh("errorVariable", BooleanType())
    def rec(expr: Expr, from: Seq[Variable], to: Seq[Variable], fromf: FunDef, tof: FunDef): Expr = {
      new SelfTreeTransformer {
        override def transform(expr: Expr): Expr = expr match {
          case v: Variable => {
            if(from.indexOf(v) != -1) to(from.indexOf(v))
            else errorVariable
          }
          case FunctionInvocation(n, t, p) => {
            val newp = p.map(elem => rec(elem, from, to, fromf, tof))
            if (newp.filter(elem => elem == errorVariable).size != 0) errorVariable
            else if(n != fromf.id) FunctionInvocation(n, t, newp)
            else FunctionInvocation(tof.id, t, newp)
          }
          case _ => super.transform(expr)
        }
      }.transform(expr)
    }
    
    val res = rec(expr, from, to, fromf, tof)
    if(res == errorVariable) None
    else Some(res)
  }
  
}

object Trace {
  def apply(ts: Trees, tt: termination.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new Trace {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}