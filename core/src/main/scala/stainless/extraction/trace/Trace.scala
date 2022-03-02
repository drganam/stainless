/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package trace

import stainless.utils.CheckFilter

trait Trace extends CachingPhase with IdentityFunctions with IdentitySorts { self =>
  val s: Trees
  val t: termination.Trees
  import s._

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] object identity extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  private def evaluate(syms: s.Symbols, expr: Expr) = {
    type ProgramType = inox.Program{val trees: Trace.this.s.type; val symbols: syms.type}
    val prog: ProgramType = inox.Program(self.s)(syms)

    val evaluator = new {
    val context = self.context
    val program: prog.type = prog
    val semantics = new inox.Semantics {
      val trees: self.s.type = self.s
      val symbols: syms.type = syms
      val program: prog.type = prog
      def createEvaluator(ctx: inox.Context) = ???
      def createSolver(ctx: inox.Context) = ???
    }
  } with evaluators.RecursiveEvaluator
    with inox.evaluators.HasDefaultGlobalContext
    with inox.evaluators.HasDefaultRecContext

    evaluator.eval(expr)
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    import symbols._
    import exprOps._

    def checkArgs(model: Identifier, norm: Identifier) = {
      val m = symbols.functions(model)
      val n = symbols.functions(norm)

      n.params.size >= 1 && n.params.init.size == m.params.size && n.tparams.size == m.tparams.size &&
      n.params.zip(n.params).forall(arg => arg._1.tpe == arg._2.tpe)
    }

    if (Trace.getModels.isEmpty) {
      val models = symbols.functions.values.toList.filter(elem => !elem.flags.exists(_.name == "library") &&
        isModel(elem.id)).map(elem => elem.id)
      Trace.setModels(models)
      Trace.nextModel
    }

    if (Trace.getFunctions.isEmpty) {
      val functions = symbols.functions.values.toList.filter(elem => !elem.flags.exists(_.name == "library") &&
        shouldBeChecked(elem.id)).map(elem => elem.id)
      Trace.setFunctions(functions)
      Trace.nextFunction
    }

    if (Trace.getNorm.isEmpty) {
      val normOpt = symbols.functions.values.toList.find(elem => isNorm(elem.id)).map(elem => elem.id)

      (Trace.getModel, normOpt) match {
        case (Some(model), Some(norm)) if checkArgs(model, norm) =>
          Trace.setNorm(normOpt)
        case _ =>
      }
    }

    symbols.functions.values.toList.foreach(fd => if (fd.flags.exists(elem => elem.name == "mkTest"))
      Trace.setMkTest(fd.id))

    def generateEqLemma: List[s.FunDef] = {

      def evalCheck(f: FunDef, m: FunDef): Boolean = {

        //improvement: there could be functions with same counterexample values; use distinct mappings;
        val counterexamples = (Trace.state.values zip Trace.state.keys).map(elem => (elem._1.counterexample, elem._2)).filter(!_._1.isEmpty).map(elem => (elem._1.get, elem._2)).filterNot(_._1.existing).filterNot(_._1.counterexample.isEmpty).filterNot(_._1.fromEval)


        def passesAllNewTests = counterexamples.forall(counterexample => {
          val pair = counterexample._1
          val fun = pair.prog.symbols.functions(counterexample._2)
          val mod = pair.prog.symbols.functions(Trace.state(fun.id).path.head)
          val ref = if (pair.fromFunction) fun else mod


          val bval = {
            type ProgramType = inox.Program{val trees: pair.prog.trees.type; val symbols: pair.prog.symbols.type}
            val prog: ProgramType = pair.prog.asInstanceOf[ProgramType]
            val syms: prog.symbols.type = prog.symbols

            val evaluator = new {
              val context = self.context
              val program: prog.type = prog
              val semantics = new inox.Semantics {
              val trees: prog.trees.type = prog.trees
              val symbols: syms.type = prog.symbols
              val program: prog.type = prog
              def createEvaluator(ctx: inox.Context) = ???
              def createSolver(ctx: inox.Context) = ???
            }
            } with inox.evaluators.RecursiveEvaluator
              with inox.evaluators.HasDefaultGlobalContext
              with inox.evaluators.HasDefaultRecContext

            val expr = syms.functions(f.id).fullBody
            val counterex = pair.counterexample

            //.get breaks if parameter names are not the same 
            //fix: store the info wheter the counterexample comes from the model or the function
            try {
            val invocation = evaluator.program.trees.FunctionInvocation(f.id, Seq(), ref.params.map(vd => 
              pair.counterexample.collectFirst({ case (k, v) if(k.id.name == vd.id.name) => v }).get))

            val invocationM = evaluator.program.trees.FunctionInvocation(m.id, Seq(), ref.params.map(vd => 
              pair.counterexample.collectFirst({ case (k, v) if(k.id.name == vd.id.name) => v }).get))

             
            (evaluator.eval(invocation), evaluator.eval(invocationM)) match {
              case (inox.evaluators.EvaluationResults.Successful(output), inox.evaluators.EvaluationResults.Successful(expected)) => {
                if(output != expected) Trace.storeCounterexample(Some(new Trace.Pair {
                  val prog = pair.prog
                  val counterexample = pair.counterexample.asInstanceOf[Map[this.prog.trees.ValDef,this.prog.trees.Expr]]
                  val existing = false
                  val fromEval = true
                  val fromFunction = pair.fromFunction
                } ))
                output == expected
              }
              case _ => 
                true
            }
            }catch {
              case e => 
                true
            }

          }
          bval 
        })

        def passesAllTests = Trace.getMkTest match { //todo just check for annotation here
          case Some(t) => {
            val test = symbols.functions(t)

            val r: Range = 1 to 5  //todo fix range

            r.forall(i => {
              val bval = {

                val getInput = s.TupleSelect(FunctionInvocation(test.id, test.tparams.map(_.tp), Seq(IntegerLiteral(i))), 1)
                val getRes = s.TupleSelect(FunctionInvocation(test.id, test.tparams.map(_.tp), Seq(IntegerLiteral(i))), 2)

                (evaluate(symbols, getInput), evaluate(symbols, getRes)) match {
                  case (inox.evaluators.EvaluationResults.Successful(input), inox.evaluators.EvaluationResults.Successful(res)) => {
                    val paramVars = input match {
                      case Tuple(pvars) => pvars
                      case pvar => Seq(pvar)
                    }
                    val evalF = s.FunctionInvocation(f.id, f.tparams.map(_.tp), paramVars)
                    evaluate(symbols, evalF) match {
                      case inox.evaluators.EvaluationResults.Successful(output) => {
                        val counterexample = (f.params zip paramVars).toMap
                        if(output != res) {
                          val p = Trace.a(inox.Program(self.s)(symbols))(counterexample)
                          Trace.storeCounterexample(p)
                        }
                        output == res
                      }
                      case _ => true
                    }
                  }
                  case _ => true
                }

              }
              bval 
            })

          } 
          case None => {
            true
          }
        }

        passesAllTests && passesAllNewTests

      }

      // Finds all the function calls in the body of fd
      def getFunCalls(fd: FunDef): List[FunDef] = {
        var funs: List[Identifier] = List()
        s.exprOps.preTraversal {
          case fi @ s.FunctionInvocation(tfd, tps, args) if tfd != fd.id //symbols.isRecursive(tfd) 
            => funs = tfd::funs
          case _ => 
        }(fd.fullBody)
        funs.distinct.map(symbols.functions(_))
      }

      // f1Calls: functions that are called from f1
      // f2Calls: functions that are called from f2
      // returns a list of sublemmas for each candidate pair (same signature + name?) + replacement map
      //ret._1 sublemma + its sublemmas and replacement
      //ret._2 and ret._3 map for replacement
      def makeSublemmas(fd1: s.FunDef, fd2: s.FunDef): List[(List[s.FunDef], s.FunDef, s.FunDef)] = {
        val f1Calls = getFunCalls(fd1)
        val f2Calls = getFunCalls(fd2)
        for (
          m <- f1Calls;
          f <- f2Calls
          if (m != f && m.params.size == f.params.size && checkArgs(m.id, f.id) && m.returnType == f.returnType) // TODO  && same arg types, names ...
        ) yield (equivalenceCheck(m, f, true), m, f) 
      }


      
     // call to eqCheck *12
     // call to makeSublemmas
     // call to eqCheck +12 returns (+12lemma, idlemma, replacement) //problem: keep idlemma + replacement


      def equivalenceCheck(fd1: s.FunDef, fd2: s.FunDef, sublemmaGeneration: Boolean): List[s.FunDef] = {
        val freshId = FreshIdentifier(CheckFilter.fixedFullName(fd1.id) + "$" + CheckFilter.fixedFullName(fd2.id))
        val eqLemma = exprOps.freshenSignature(fd1).copy(id = freshId)

        val sublemmas = if (sublemmaGeneration) makeSublemmas(fd1, fd2) else List() 

        println("list of sublemmas:")
        println(sublemmas)

        //body of fd2, with calls to subfunctions replaced
        val replacement: List[FunDef] = sublemmas match {
          case Nil => List()
          case _ => 
            val sm = sublemmas.map(_._2).map(_.id)
            val sf = sublemmas.map(_._3).map(_.id)
            List(inductPattern(symbols, fd2, fd2, "replacement", (sf zip sm).toMap).setPos(fd2.getPos).copy(flags = Seq(s.Derived(Some(fd2.id)))))
        }

        println("latest replacement")
        println(replacement)

        val newParamTps = eqLemma.tparams.map{tparam => tparam.tp}
        val newParamVars = eqLemma.params.map{param => param.toVariable}

        val fdSpecs = if(Trace.funFirst) fd2 else fd1 

        val subst = (fdSpecs.params.map(_.id) zip newParamVars).toMap
        val tsubst = (fdSpecs.tparams zip newParamTps).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
        val specializer = new Specializer(eqLemma, eqLemma.id, tsubst, subst, Map())

        val specs = BodyWithSpecs(fdSpecs.fullBody).specs.filter(s => s.kind == LetKind || s.kind == PreconditionKind) 
        val pre = specs.map(spec => spec match {
          case Precondition(cond) => Precondition(specializer.transform(cond))
          case LetInSpec(vd, expr) => LetInSpec(vd, specializer.transform(expr))
        })

        val fun1 = s.FunctionInvocation(fd1.id, newParamTps, newParamVars)
        val fun2 = replacement match {
          case Nil => s.FunctionInvocation(fd2.id, newParamTps, newParamVars)
          case h::t => s.FunctionInvocation(h.id, newParamTps, newParamVars)
        }


        val (normFun1, normFun2) = Trace.getNorm match {
          case Some(n) if (checkArgs(fun1.id, n)) => ( //normalization does not work for sublemmas
            s.FunctionInvocation(n, newParamTps, newParamVars :+ fun1), 
            s.FunctionInvocation(n, newParamTps, newParamVars :+ fun2))
          case _ => (fun1, fun2)
        }

        val res = s.ValDef.fresh("res", s.UnitType())
        val cond = s.Equals(normFun1, normFun2) 

        val post = Postcondition(Lambda(Seq(res), cond)) 

        val body = s.UnitLiteral()
        val withPre = exprOps.reconstructSpecs(pre, Some(body), s.UnitType())

        println("lemma's id before the transformation:")
        println(eqLemma.id)

        


        // return the @traceInduct annotated eqLemma
        // + potential sublemmas
        // + the coressponding replacement functions
        (eqLemma.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
          flags = Seq(s.Derived(Some(fd1.id)), s.Annotation("traceInduct",List(StringLiteral(fd1.id.name)))),
          returnType = s.UnitType()
        ).copiedFrom(eqLemma) :: sublemmas.flatMap(_._1)) ++ replacement
      }

      (Trace.getModel, Trace.getFunction) match {
        case (Some(model), Some(function)) => {
          val m = symbols.functions(model)
          val f = symbols.functions(function)

          Trace.nextEqCheckState

          if (m.params.size == f.params.size && evalCheck(f, m)) {
            val res: List[s.FunDef] = Trace.eqCheckState match {
              case Trace.EqCheckState.ModelFirst => 
                equivalenceCheck(m, f, false)
              case Trace.EqCheckState.FunFirst =>
                equivalenceCheck(f, m, false)
              case Trace.EqCheckState.ModelFirstWithSublemmas =>
                equivalenceCheck(m, f, true)
            }

            res match {
              case t::sublemmas =>
                Trace.setTrace(t.id)
                Trace.sublemmas = sublemmas.map(_.id)
              case _ => 
            }                
            res
          }
          else {
            Trace.resetTrace
            Trace.resetEqCheckState
            List()
          }
        }
        case _ => {
          List()
        }
      }
    }

    //println(generateEqLemma)

    val generatedFunctions = generateEqLemma
    val functions = generatedFunctions ++ symbols.functions.values.toList

    val inductFuns = functions.toList.flatMap(fd => if (fd.flags.exists(elem => elem.name == "traceInduct")) {
      //find the model for fd
      var funInv: Option[s.FunctionInvocation] = None
      fd.flags.filter(elem => elem.name == "traceInduct").head match {
        case s.Annotation("traceInduct", fun) => {
          BodyWithSpecs(fd.fullBody).getSpec(PostconditionKind) match {
            case Some(Postcondition(post)) => 
              s.exprOps.preTraversal {
                case _ if funInv.isDefined => // do nothing
                case fi @ s.FunctionInvocation(tfd, tps, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
                => {
                      val paramVars = fd.params.map(_.toVariable)
                      val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
                      if (argCheck) funInv = Some(fi)
                    }
                case _ => 
              }(post)
            case _ => 
          }
        }
      }

      funInv match {
        case Some(finv) => {

          //TODO consider MAKING THE SUBLEMMA PART HERE
          // benefits: works for @traceInduct when not in batched mode
          // + easier to set it in the Trace object
          // downsides: this part is not super recursive, not sure about going one level deeper

          // make a helper lemma:
          val helper = inductPattern(symbols, symbols.functions(finv.id), fd, "indProof", Map()).setPos(fd.getPos)
          //println(helper)

          val returnType = typeOps.instantiateType(helper.returnType, (helper.typeArgs zip fd.typeArgs).toMap)

          // transform the main lemma
          val proof = FunctionInvocation(helper.id, finv.tps, fd.params.map(_.toVariable))

          val body = Let(s.ValDef.fresh("ind$proof", returnType), proof, exprOps.withoutSpecs(fd.fullBody).get)
          val withPre = exprOps.reconstructSpecs(BodyWithSpecs(fd.fullBody).specs, Some(body), fd.returnType)

          val lemma = fd.copy(
            fullBody = BodyWithSpecs(withPre).reconstructed,
            flags = (s.Derived(Some(fd.id)) +: s.Derived(Some(finv.id)) +: (fd.flags.filterNot(f => f.name == "traceInduct"))).distinct
          ).copiedFrom(fd).setPos(fd.getPos)

          // problem: sublemmas shouldn't be set with Trace.setTrace
          // solution: annotate them as subInduct instead of traceInduct ?

          // broken: user's @traceInduct functions get in the way
          // solution: another annotation for generated equivalence lemmas OR ---> JUST DO Trace.setTrace from the other part ???
          //                                                                       problematic when generating 2 lemmas (ref first, then stud) ???
          //           keep @traceInduct for user defined lemmas
          //           also use @traceInduct for sublemmas


          println("lemma:")
          println(lemma.id)
          println("sublemmas of the lemma at the end:")
          println(Trace.sublemmas)


          //Trace.setTrace(lemma.id)
          //Trace.setProof(helper.id)
          println("lemma")
          println(lemma.fullBody)
          Trace.getTrace match {
            case Some(t) if(t == lemma.id) =>
              println(" alive") 
              Trace.setProof(helper.id)
            case _ => 
          }
          println("still alive")

          if(Trace.sublemmas.contains(lemma.id)) Trace.sublemmas = helper.id :: Trace.sublemmas


          List(helper, lemma)
        }
        case None => {
          val lemma = fd.copy(
            flags = (s.Derived(Some(fd.id)) +: (fd.flags.filterNot(f => f.name == "traceInduct")))
          ).copiedFrom(fd).setPos(fd.getPos)
          //Trace.setTrace(lemma.id)
          List(lemma)
        }
      }
    } else List())

    val extractedSymbols = super.extractSymbols(context, symbols)
    
    val extracted = t.NoSymbols
      .withSorts(extractedSymbols.sorts.values.toSeq)
      .withFunctions((generatedFunctions.map(fun => identity.transform(fun)) ++ extractedSymbols.functions.values).filterNot(fd => fd.flags.exists(elem => elem.name == "traceInduct")).toSeq)

    registerFunctions(extracted, inductFuns.map(fun => identity.transform(fun)))
  }

  def inductPattern(symbols: s.Symbols, model: FunDef, lemma: FunDef, suffix: String, replacement: Map[Identifier, Identifier]) = {
    import symbols._
    import exprOps._

    val indPattern = exprOps.freshenSignature(model).copy(id = FreshIdentifier(lemma.id+ "$" + suffix))
    val newParamTps = indPattern.tparams.map{tparam => tparam.tp}
    val newParamVars = indPattern.params.map{param => param.toVariable}

    val fi = FunctionInvocation(model.id, newParamTps, newParamVars)

    val tpairs = model.tparams zip fi.tps
    val tsubst = tpairs.map { case (tparam, targ) => tparam.tp.id -> targ } .toMap
    val subst = (model.params.map(_.id) zip fi.args).toMap
    val specializer = new Specializer(model, indPattern.id, tsubst, subst, replacement)
    
    val fullBodySpecialized = specializer.transform(exprOps.withoutSpecs(model.fullBody).get) 

    val specsSubst = (lemma.params.map(_.id) zip newParamVars).toMap ++ (model.params.map(_.id) zip newParamVars).toMap
    val specsTsubst = ((lemma.tparams zip fi.tps) ++ (model.tparams zip fi.tps)).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
    val specsSpecializer = new Specializer(indPattern, indPattern.id, specsTsubst, specsSubst, Map())

    //TODO check
    //val specs = BodyWithSpecs(model.fullBody).specs
    val specs = BodyWithSpecs(model.fullBody).specs ++ BodyWithSpecs(lemma.fullBody).specs.filterNot(_.kind == MeasureKind)
    val pre = specs.filterNot(_.kind == PostconditionKind).map(spec => spec match {
      case Precondition(cond) => Precondition(specsSpecializer.transform(cond)).setPos(spec)
      case LetInSpec(vd, expr) => LetInSpec(vd, specsSpecializer.transform(expr)).setPos(spec)
      case Measure(measure) => Measure(specsSpecializer.transform(measure)).setPos(spec)
      case s => context.reporter.fatalError(s"Unsupported specs: $s")
    })

    val withPre = exprOps.reconstructSpecs(pre, Some(fullBodySpecialized), indPattern.returnType)

    val speccedLemma = BodyWithSpecs(lemma.fullBody).addPost
    val speccedOrig = BodyWithSpecs(model.fullBody).addPost
    val postLemma = speccedLemma.getSpec(PostconditionKind).map(post => 
      specsSpecializer.transform(post.expr))
    val postOrig = speccedOrig.getSpec(PostconditionKind).map(post => specsSpecializer.transform(post.expr))
    
    (postLemma, postOrig) match {
      case (Some(Lambda(Seq(res1), cond1)), Some(Lambda(Seq(res2), cond2))) => 
        val res = ValDef.fresh("res", indPattern.returnType)
        val freshCond1 = exprOps.replaceFromSymbols(Map(res1 -> res.toVariable), cond1)
        val freshCond2 = exprOps.replaceFromSymbols(Map(res2 -> res.toVariable), cond2)

        val cond = andJoin(Seq(freshCond1, freshCond2))
        val post = Postcondition(Lambda(Seq(res), cond))

        indPattern.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
          flags = Seq(s.Derived(Some(lemma.id)), s.Derived(Some(model.id)))
        ).copiedFrom(indPattern)
    }

  }

  class Specializer(
      origFd: FunDef,
      newId: Identifier,
      tsubst: Map[Identifier, Type],
      vsubst: Map[Identifier, Expr],
      replacement: Map[Identifier, Identifier]
    ) extends s.SelfTreeTransformer {

      override def transform(expr: s.Expr): t.Expr = expr match {
        case v: Variable =>
          vsubst.getOrElse(v.id, super.transform(v))

        case fi: FunctionInvocation if fi.id == origFd.id =>
          val fi1 = FunctionInvocation(newId, tps = fi.tps, args = fi.args)
          super.transform(fi1.copiedFrom(fi))

        case fi: FunctionInvocation if replacement.contains(fi.id) =>
          val fi1 = FunctionInvocation(replacement.getOrElse(fi.id, fi.id), tps = fi.tps, args = fi.args)
          super.transform(fi1.copiedFrom(fi))

        case _ => super.transform(expr)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case tp: TypeParameter =>
          tsubst.getOrElse(tp.id, super.transform(tp))

        case _ => super.transform(tpe)
      }
    }

  type Path = Seq[String]

  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optCompareFuns) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private lazy val pathsOptModels: Option[Seq[Path]] = context.options.findOption(optModels) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private lazy val pathsOptNorm: Option[Seq[Path]] = 
    Some(Seq(context.options.findOptionOrDefault(optNorm)).map(CheckFilter.fullNameToPath))

  private def shouldBeChecked(fid: Identifier): Boolean = shouldBeChecked(pathsOpt, fid)
  private def isModel(fid: Identifier): Boolean = shouldBeChecked(pathsOptModels, fid)
  private def isNorm(fid: Identifier): Boolean = shouldBeChecked(pathsOptNorm, fid)

  private def shouldBeChecked(paths: Option[Seq[Path]], fid: Identifier): Boolean = paths match {
    case None => false

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumed.
      val path: Path = CheckFilter.fullNameToPath(CheckFilter.fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }
}

object Trace {
  var clusters: Map[Identifier, List[Identifier]] = Map()
  var errors: List[Identifier] = List()
  var unknowns: List[Identifier] = List()
  var wrong: List[Identifier] = List() //bad signature

  object Status extends Enumeration {
    type Status = Value
    val Unchecked, Valid, Unknown, Errorneus, Wrong = Value
  }

  import Status._

  case class State(var status: Status, var path: List[Identifier], var counterexample: Option[Pair], var prevModels: List[Identifier])

  var state: Map[Identifier, State] = Map()

  def optionsError(implicit ctx: inox.Context): Boolean = 
    !ctx.options.findOptionOrDefault(frontend.optBatchedProgram) && 
    (!ctx.options.findOptionOrDefault(optModels).isEmpty || !ctx.options.findOptionOrDefault(optCompareFuns).isEmpty)
      
  def printEverything(implicit ctx: inox.Context) = {
    import ctx.{ reporter, timers }
    println("rank list")
    println(allModels)
    println(allModels.toList.sortBy(m => -m._2).map(_._1).take(5).map(CheckFilter.fixedFullName))
    if(!clusters.isEmpty || !errors.isEmpty || !unknowns.isEmpty || !wrong.isEmpty) {
      reporter.info(s"Printing equivalence checking results:")  
      allModels.keys.foreach(model => if (!clusters(model).isEmpty) {
        val l = clusters(model).map(CheckFilter.fixedFullName).mkString(", ")
        val m = CheckFilter.fixedFullName(model)
        reporter.info(s"List of functions that are equivalent to model $m: $l")
      })

      val errorneous = errors.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of erroneous functions: $errorneous")
      val timeouts = unknowns.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of timed-out functions: $timeouts")
      val wrongs = wrong.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of wrong functions: $wrongs")

      reporter.info(s"Printing the final state:")  
      allFunctions.foreach(f => {
        val l = state(f).path.map(CheckFilter.fixedFullName).mkString(", ")
        val m = CheckFilter.fixedFullName(f)
        reporter.info(s"Path for the function $m: $l")
      })
      /*
      allFunctions.foreach(f => {
        val c = state(f).counterexample match {
          case None => None
          case Some(co) => (co.counterexample, co.fromEval)
        }
        val m = CheckFilter.fixedFullName(f)
        reporter.info(s"Counterexample for the function $m: $c")
      })
      */
    }

  }

  var allModels: Map[Identifier, Int] = Map()
  var tmpModels: List[Identifier] = List()

  var allFunctions: List[Identifier] = List()
  var tmpFunctions: List[Identifier] = List()

  var model: Option[Identifier] = None
  var function: Option[Identifier] = None
  var norm: Option[Identifier] = None
  var trace: Option[Identifier] = None
  var proof: Option[Identifier] = None //TODO idea: store it within sublemmas
  var mkTest: Option[Identifier] = None

  var sublemmas: List[Identifier] = List()

  var sublemmaGeneration: Boolean = false

  object EqCheckState extends Enumeration {
    type EqCheckState = Value
    val InitState, ModelFirst, FunFirst, ModelFirstWithSublemmas = Value
  }

  var eqCheckState = EqCheckState.InitState // skip if !symbols.isRecursive(model) && symbols.isRecursive(function) ?

  def nextEqCheckState: Unit = eqCheckState = eqCheckState match {
    case EqCheckState.InitState => EqCheckState.ModelFirst
    case EqCheckState.ModelFirst => EqCheckState.FunFirst
    case EqCheckState.FunFirst => EqCheckState.ModelFirstWithSublemmas //  skip if there are no sublemmas ?
    case EqCheckState.ModelFirstWithSublemmas => EqCheckState.ModelFirst  //skip if there are no sublemmas ?
  }
  
  def resetEqCheckState = eqCheckState = EqCheckState.InitState
  def isFinalEqCheckState = eqCheckState == EqCheckState.ModelFirstWithSublemmas

  def funFirst = eqCheckState == EqCheckState.FunFirst


          //btw if any of the sublemmas is wrong, only classify as timeout
          //if all the sublemmas are ok but the main is wrong, classify as wrong


  var cnt = 0

  def apply(ts: Trees, tt: termination.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new Trace {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }

  def setModels(m: List[Identifier]) = {
    allModels = m.map(elem => (elem, 100)).toMap
    tmpModels = m
    clusters = (m zip m.map(_ => Nil)).toMap
    state = state ++ (m zip m.map(_ => State(Valid, List(), None, List()))).toMap
  }

  def setFunctions(f: List[Identifier]) = {
    allFunctions = f
    tmpFunctions = f
    cnt = f.size
    state = state ++ (f zip f.map(_ => State(Unchecked, List(), None, List()))).toMap
  }

  def getModels = allModels

  def getFunctions = allFunctions

  //model for the current iteration
  def getModel = model

  //function to check in the current iteration
  def getFunction = function

  def getNorm = norm

  def getMkTest = mkTest

  def setTrace(t: Identifier) = {
    proof = None // TODO this is a recent change
    trace = Some(t)
    state(function.get).prevModels = model.get :: state(function.get).prevModels
  }

  def getTrace = trace

  def setProof(p: Identifier) = proof = Some(p)

  def setNorm(n: Option[Identifier]) = norm = n
  def setMkTest(t: Identifier) = mkTest = Some(t)

  def resetTrace = {
    trace = None
    proof = None
    sublemmas = List()
  }

  //iterate model for the current function
  def nextModel = tmpModels match {
    case x::xs => { 
      tmpModels = xs
      model = Some(x)
    }
    case Nil => model = None
  }

  //iterate function to check; reset model
  def nextFunction = {
    trace = None
    proof = None
      tmpFunctions match {
      case x::xs => {
        //val modsize = allModels.filterNot(state(x).prevModels.contains).size
        //val n = if (modsize < 50) modsize else if(modsize < 100) 70 else 3
        //tmpModels = allModels.filterNot(state(x).prevModels.contains).take(n)

        val n = 5
        tmpModels = allModels.toList.sortBy(m => -m._2).map(_._1).filterNot(state(x).prevModels.contains).take(n)

        //case without priorities
        //tmpModels = allModels.toList.map(_._1).filterNot(state(x).prevModels.contains).take(n)

        if(tmpModels.isEmpty) tmpModels = allModels.keys.take(1).toList //todo fix to skip this function
        nextModel
        tmpFunctions = xs
        function = Some(x)
      }
      case Nil => {
        function = None
      }
    }
  }

  var counter = 0

  trait Pair { 
    val prog: inox.Program
    val counterexample: Map[prog.trees.ValDef, prog.trees.Expr]
    val existing: Boolean
    val fromFunction: Boolean
    val fromEval: Boolean
  }

  var pair: Option[Pair] = None

  def a(pr: inox.Program)(counterex: Map[pr.trees.ValDef, pr.trees.Expr]): Option[Pair]  = {
    pair = Some(new Pair {
          val prog: pr.type = pr
          val counterexample = counterex
          val existing = true
          val fromEval = true
          val fromFunction = false
      })
    pair
  }

  def shouldVerify(fun: Identifier) = {
    !function.isEmpty && function.get == fun ||
    !proof.isEmpty && proof.get == fun ||
    !trace.isEmpty && trace.get == fun
  }

  def f(pr: inox.Program)(counterex: pr.Model)(fun: Identifier): Unit = {
    val ok = !function.isEmpty && function.get == fun ||
             !proof.isEmpty && proof.get == fun ||
             !trace.isEmpty && trace.get == fun
    if(ok) {
      pair = Some(new Pair {
          val prog: pr.type = pr
          val counterexample = counterex.vars
          val existing = false
          val fromEval = false
          val fromFunction = function.get == fun || funFirst
      })
    } 
  }

  // TODO cleaning + check validity of sublemmas
  def nextIteration[T <: AbstractReport[T]](report: AbstractReport[T])(implicit context: inox.Context): Boolean = {
    counter = counter + 1
    if(counter % 10 == 0) printEverything

     println("lemma form nextIteration loop lemma form nextIteration loop lemma form nextIteration loop")
     println(trace)
     //println("sublemmas validity: sublemmas and then if there are no errors nor unknowns")
      //println(sublemmas(t))

    val sublemmasAreValid = sublemmas.forall(s => !report.hasError(s) && !report.hasUnknown(s))

    (function, proof, trace) match {
      case (Some(f), Some(p), Some(t)) => {
        if (report.hasError(f) || report.hasError(p) || report.hasError(t)) {
          reportError(pair) //TODO only if not in the sublemma state
        }
        else if (report.hasUnknown(f) || report.hasUnknown(p) || report.hasUnknown(t)) reportUnknown
        else {
          println("report valid")
          println("lemma")
          println(t)
          println("sublemmas validity: sublemmas and then if there are no errors nor unknowns")
          println(sublemmas)
          println(sublemmas.forall(s => !report.hasError(s) && !report.hasUnknown(s)))

          if (sublemmasAreValid) reportValid
          else reportUnknown
        }
      }
      case (Some(f), _, Some(t)) => {
        if (report.hasError(f) || report.hasError(t)) reportError(pair)
        else if (report.hasUnknown(f) || report.hasUnknown(t)) reportUnknown
        else if (sublemmasAreValid) reportValid
        else reportUnknown
      }
      case (Some(f), _, _) if(state(f).counterexample != None) =>
        reportError(state(f).counterexample)
        counter = counter - 1
      case _ => reportWrong
    }
    
    if(isDone && unknowns.size < cnt) {
      cnt = unknowns.size
      tmpModels = allModels.keys.toList //only the new ones
      tmpFunctions = unknowns
      unknowns = List()
      nextFunction
    }
    if(isDone) {
      System.out.println("COUNTER - NUMBER OF ITERATIONS AND GENERATED PROOFS")
      System.out.println(counter)
    }

    !isDone
  }

  private def isDone = function == None

  private def storeCounterexample(counterexample: Option[Pair]) = {
    state(function.get).counterexample = counterexample
  }

  private def reportError[T](counterexample: Option[Pair]) = {
    resetEqCheckState
    errors = function.get::errors //store counter-example
    unknowns = unknowns.filterNot(elem => elem == function.get)
    state(function.get).status = Errorneus
    state(function.get).path = model.get +: state(model.get).path
    state(function.get).counterexample = counterexample
    nextFunction
  }

  
  //if there is a new state go there, otherwise report as unknown
  private def reportUnknown = {
    allModels = allModels.updated(model.get, allModels(model.get)-1)
    if (isFinalEqCheckState) {
      resetEqCheckState
      nextModel
      if (model == None) {
        unknowns = function.get::unknowns
        nextFunction
      }
    }
    else {
      //nextEqCheckState
    }
  }

  private def reportValid = {
    resetEqCheckState
    if (!allModels.keys.toList.contains(function.get)) {
      state(function.get).status = Valid
      state(function.get).path = model.get +: state(model.get).path
      //allModels = (allModels :+ function.get).sortBy(m => -state.values.flatMap(_.path).count(_ == m))

      val inc = if (allModels(model.get) > 0) 20 else 100
      allModels = allModels.updated(model.get, allModels(model.get) + inc)
      allModels = (allModels + (function.get -> 0))//.sortBy(m => -m._2)


      //allModels = (allModels :+ function.get).sortBy(m => -state.values.flatMap(_.path).count(_ == m))  //sortBy(m => state(m).path.size)
      //allModels = (allModels :+ function.get)
      clusters = clusters + (function.get -> List())
    }

    clusters = clusters + (model.get -> (function.get::clusters.getOrElse(model.get, List())))
    unknowns = unknowns.filterNot(elem => elem == function.get)
    nextFunction
  }

  private def reportWrong = {
    resetEqCheckState
    if (function != None) wrong = function.get::wrong
    unknowns = unknowns.filterNot(elem => elem == function.get)
    resetTrace
    nextFunction
  }

}