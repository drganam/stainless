/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package induction

trait Induction extends CachingPhase with SimpleFunctions with IdentitySorts { self =>
  val s: Trees
  val t: trace.Trees
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
    val result: FunDef = if(fd.flags.contains(FunEq)) {
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
    
    identity.transform(result.copy(flags = result.flags filterNot (f => f == FunEq)))
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
    
    fInduct.fullBody match {
      case MatchExpr(_,_) => {
        funInduct(symbols, fd, fInduct.copy(fInduct.id, fInduct.tparams, fInduct.params, fInduct.returnType, matchToIfThenElse(fInduct.fullBody), fInduct.flags))
      }
      case IfExpr(cond, thenn, elze) => {
        val nCond = replaceSymbols(cond, fInduct.params.map(elem => elem.toVariable), fd.params.map(elem => elem.toVariable), fInduct, fd) 
        nCond match {
          case Some(newCond) => {
            if(containsRecursiveCalls(thenn, fInduct)) {
              val name = exprOps.functionCallsOf(thenn).filter(elem => elem.id == fInduct.id).head
              replaceSymbols(name, fInduct.params.map(elem => elem.toVariable), fd.params.map(elem => elem.toVariable), fInduct, fd) match {
                case None => None
                case Some(newThenn) => Some(IfExpr(newCond, newThenn, BooleanLiteral(true))) 
              }
            }
            else if(containsRecursiveCalls(elze, fInduct)) {
              val name = exprOps.functionCallsOf(elze).filter(elem => elem.id == fInduct.id).head
              replaceSymbols(name, fInduct.params.map(elem => elem.toVariable), fd.params.map(elem => elem.toVariable), fInduct, fd) match {
                case None => None
                case Some(newElze) => Some(IfExpr(newCond, BooleanLiteral(true), newElze)) 
              }
            }
            else None 
          }
          case None => None
        }
      }
      case _ => None
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

object Induction {
  def apply(ts: Trees, tt: trace.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new Induction {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}