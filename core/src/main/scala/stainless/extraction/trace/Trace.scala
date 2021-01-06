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

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    import symbols._
    import trees._

    var localCounter = 0

    def freshId(): Identifier = {
      localCounter = localCounter + 1
      new Identifier("x"+localCounter,localCounter,localCounter)
    }

    def newFuns(funs1: List[s.FunDef], funs2: List[s.FunDef], acc: List[t.FunDef]): List[t.FunDef] = {
      funs1 match {
        case Nil => acc
        case elem1::xs1 => {
          funs2 match {
            case Nil => newFuns(xs1, symbols.functions.values.toList, acc)
            case elem2::xs2 if (elem1 != elem2) => {

              //System.out.println(elem1.id)
              //System.out.println(elem2.id)

              val fd1 = extractFunction(symbols, elem1) //elem1 //identity.transform(elem1.copy(id = identity.transform(elem1.id)))
              val fd2 = extractFunction(symbols, elem2) //elem2 //identity.transform(elem2.copy(id = identity.transform(elem2.id)))

              //todo: check if both funs have same arg list
              val newParams = fd1.params.map{param => param.freshen}
              val newParamVars = newParams.map{param => param.toVariable}

              val newParamTypes = fd1.tparams.map{tparam => tparam.freshen}
              val newParamTps = newParamTypes.map{tparam => tparam.tp}

              val vd = t.ValDef.fresh("holds", t.BooleanType())
              val post = t.Lambda(Seq(vd), vd.toVariable)

              val body = t.Ensuring(t.Equals(t.FunctionInvocation(fd1.id, newParamTps, newParamVars), t.FunctionInvocation(fd2.id, newParamTps, newParamVars)), post)
              val flags: Seq[t.Flag] = Seq() //TraceInduct //Seq(Annotation("traceInduct", Seq()))

              //todo fresh params
              val newf = new t.FunDef(freshId(), newParamTypes, newParams, t.BooleanType(), body, flags)

              //System.out.println(newf)
              newFuns(funs1, xs2, newf::acc)
            }
            case _ => newFuns(funs1, funs2.tail, acc)
          }
        }
      }
    }

    val extracted = super.extractSymbols(context, symbols)
    val functions =  symbols.functions.values.map(elem => identity.transform(elem.copy(id = identity.transform(elem.id)))).toSeq//Seq()
    //System.out.println(symbols.functions.size)

    val funs = newFuns(symbols.functions.values.toList, symbols.functions.values.toList, Nil)
    //funs.foreach(elem => System.out.println(elem))

    registerFunctions(extracted, funs)
  }

  protected def extractFunction1(symbols: Symbols, fd: FunDef): t.FunDef = {
    import symbols._
    //System.out.println(fd)
    var funInv: Option[FunctionInvocation] = None

          exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi @ FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd)
            => {
                  val paramVars = fd.params.map(_.toVariable)
                  val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
                  if (argCheck) 
                    funInv = Some(fi)
                }
            case _ => 
          }(fd.fullBody)


    val result: FunDef = (funInv match {
      case None => fd
      case Some(finv) => createTactFun(symbols, fd, finv)
    })

    //System.out.println(result)
    identity.transform(result.copy(flags = result.flags filterNot (f => f == TraceInduct)))    
  }


  
  override protected def extractFunction(symbols: Symbols, fd: FunDef): t.FunDef = {
    import symbols._

    //System.out.println(fd)

    var funInv: Option[FunctionInvocation] = None

    if(fd.flags.exists(elem => elem.name == "traceInduct")) {
      fd.flags.filter(elem => elem.name == "traceInduct").head match {
        case Annotation("traceInduct", fun) => {
          exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi @ FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
            => {
                  val paramVars = fd.params.map(_.toVariable)
                  val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
                  if (argCheck) 
                    funInv = Some(fi)
                }
            case _ => 
          }(fd.fullBody)
        }
      }
    }

    val result: FunDef = (funInv match {
      case None => fd
      case Some(finv) => createTactFun(symbols, fd, finv)
    })


    identity.transform(result.copy(flags = result.flags filterNot (f => f == TraceInduct)))    
  }
  
  private def createTactFun(symbols: Symbols, function: FunDef, finv: FunctionInvocation): FunDef = {
    import symbols._

    val callee: FunDef = symbols.functions.filter(elem => elem._2.id == finv.id).head._2

    def inductPattern(e: Expr): Expr = {
      e match {
        case IfExpr(c, th, el) =>
          andJoin(Seq(inductPattern(c), IfExpr(c, inductPattern(th), inductPattern(el))))
        case MatchExpr(scr, cases) =>
          val scrpat = inductPattern(scr)
          val casePats = cases.map {
            case MatchCase(pat, optGuard, rhs) =>
              val guardPat = optGuard.toSeq.map(inductPattern _)
              (guardPat, MatchCase(pat, optGuard, inductPattern(rhs)))
          }
          val pats = scrpat +: casePats.flatMap(_._1) :+ MatchExpr(scr, casePats.map(_._2))
          andJoin(pats)
        case Let(i, v, b) =>
          andJoin(Seq(inductPattern(v), Let(i, v, inductPattern(b))))
        case FunctionInvocation(tfd, _, args) =>
          val argPattern = andJoin(args.map(inductPattern))
          if (tfd == callee.id) { // self recursive call ?
            // create a tactFun invocation to mimic the recursion pattern
            val paramVars = function.params.map(_.toVariable)
            val paramIndex = paramVars.zipWithIndex.toMap
            val framePositions = finv.args.zipWithIndex.collect {
              case (v: Variable, i) if paramVars.contains(v) => (v, i)
            }.toMap
            val footprint = paramVars.filterNot(framePositions.keySet.contains)
            val indexedFootprint = footprint.map { a => paramIndex(a) -> a }.toMap
            // create a tactFun invocation to mimic the recursion pattern
            val indexedArgs = framePositions.map {
              case (f, i) => paramIndex(f) -> args(i)
            }.toMap ++ indexedFootprint
            val recArgs = (0 until indexedArgs.size).map(indexedArgs)
            val recCall = FunctionInvocation(function.id, function.typeArgs, recArgs)

            andJoin(Seq(argPattern, recCall))
          } else {
            argPattern
          }
        case Operator(args, op) =>
          // conjoin all the expressions and return them
          andJoin(args.map(inductPattern))
      }
    }

    val argsMap = callee.params.map(_.toVariable).zip(finv.args).toMap
    val tparamMap = callee.typeArgs.zip(finv.tfd.tps).toMap
    val inlinedBody = typeOps.instantiateType(exprOps.replaceFromSymbols(argsMap, callee.body.get), tparamMap)
    val inductScheme = inductPattern(inlinedBody)

    val prevBody = function.fullBody match {
      case Ensuring(body, pred) => body
      case _ => function.fullBody
    }

    // body, pre and post for the tactFun

    val body = andJoin(Seq(inductScheme, prevBody))
    val precondition = function.precondition
    val postcondition = function.postcondition
 
    val bodyPre = exprOps.withPrecondition(body, precondition)
    val bodyPost = exprOps.withPostcondition(bodyPre,postcondition)

    function.copy(function.id, function.tparams, function.params, function.returnType, bodyPost, function.flags)  

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