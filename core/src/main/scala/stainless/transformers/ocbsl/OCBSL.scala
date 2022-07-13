package stainless
package transformers
package ocbsl

import inox.solvers

// TODO: Certains Or ne semble pas correctement être flattened
// TODO: Not(Or(..)) => And dans uncodeOf
// TODO: Non!!!! L'ordre des disjunction a de l'importance
trait OCBSL extends Definitions {
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable // A bit ironic that we import mutable stuff right after "Purity"...

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class OEnv(conditions: Set[Code],
                  letDef: Map[VarId, (Code, Boolean)]) {
    def withCond(c: Code): OEnv = copy(conditions = conditions + c)
    def withConds(cs: Set[Code]): OEnv = copy(conditions = conditions ++ cs)

    def withLetBound(v: VarId, c: Code, canSubst: Boolean): OEnv = copy(letDef = letDef + (v -> (c, canSubst)))

    def withLetBounds(vs: Seq[(VarId, Code)], canSubst: Boolean): OEnv = withLetBounds(vs)((_, _) => canSubst)

    def withLetBounds(vs: Seq[(VarId, Code)])(canSubst: (VarId, Code) => Boolean): OEnv = {
      assert(letDef.keySet.intersect(vs.map(_._1).toSet).isEmpty)
      OEnv(conditions, letDef ++ vs.map { case (v, c) => v -> (c, canSubst(v, c)) })
    }
  }

  object OEnv {
    def empty: OEnv = OEnv(Set.empty, Map.empty)
  }

  case class InLambda(v: Boolean)

  enum Occurrence {
    case Zero
    case Once(inEnv: OEnv, inLambda: Boolean)
    case Many

    def ++(that: Occurrence): Occurrence = (this, that) match {
      case (Zero, _) => that
      case (_, Zero) => this
      case _ => Many
    }

    def isZero: Boolean = this match {
      case Zero => true
      case _ => false
    }
    def isOnce: Boolean = this match {
      case Once(_, _) => true
      case _ => false
    }
    def isMany: Boolean = this match {
      case Many => true
      case _ => false
    }
  }


  case class Usages(c2u: Map[Code, Occurrence]) {
    def apply(c: Code): Occurrence = c2u.getOrElse(c, Occurrence.Zero)

    def ++(that: Usages): Usages = Usages((c2u.keySet ++ that.c2u.keySet)
      .map(c => c -> (this(c) ++ that(c))).toMap)

    def incOccurrences(cs: Iterable[Code])(using inEnv: OEnv, inLambda: InLambda): Usages =
      this ++ Usages(cs.map(c => c -> (Occurrence.Once(inEnv, inLambda.v): Occurrence)).toMap)

    def incOccurrences(cs: Iterable[(Code, OEnv)])(using inLambda: InLambda): Usages =
      this ++ Usages(cs.map { case (c, inEnv) => c -> (Occurrence.Once(inEnv, inLambda.v): Occurrence) }.toMap)

    def incOccurrence(c: Code)(using inEnv: OEnv, inLambda: InLambda): Usages = incOccurrences(Seq(c))

    def setTo(c: Code, o: Occurrence): Usages = Usages(c2u + (c -> o))
  }

  // OEnv: En gros tous les "let bindings" des arguments pour terminal (qui peuvent être elided)
  // terminalHasLambdaDef: contient ou est un lambda soit meme
  case class CodeRes(terminal: Code, terminalHasLambdaDef: Boolean, ctx: (Usages, Code) => (Usages, Code), usages: Usages, env: OEnv) {
    // TODO: Ok????
    // TODO: Ok????
    // TODO: Ok????
    // "self plugged": on remplit le trou qu'on a crée soi-meme avec terminal: on prend donc notre env, et inLambda est false
    // (en gros: let ... in [] -> let ... in terminal, donc pas dans un lambda
    def selfPlugged: Code = {
//      val u = usages // ++ Usages.of(terminal)(using env, InLambda(false))
      val res = ctx(usages, terminal)._2
      res
    } // ctx(Usages.of(terminal)(using env, InLambda(false)))(terminal)
  }

  object Usages {
    def empty: Usages = Usages(Map.empty)

    // TODO: Dire qu'on ne compte que term lui même et pas ses composants
    def of(term: Code)(using env: OEnv, inLambda: InLambda): Usages =
      Usages(Map(term -> Occurrence.Once(env, inLambda.v)))
  }

  object CodeRes {
    // TODO: Dire qu'est-ce que c'est que ce truc!!!!
    def of(term: Code, termHasLambdaDef: Boolean)(using env: OEnv, inLambda: InLambda): CodeRes = {
      CodeRes(term, termHasLambdaDef, idCtx, Usages.of(term), env)
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???

  // TODO: On pourrait simplifier les trucs du genre !isInstanceOf[A] && isInstanceOf[B] en isInstanceOf[B] pour les patmat?

  // TODO (liste de rappel):
  //    - Pour le cache, il faudra qu'on serialize les mapping signature -> code
  //    Il faudra aussi que ce mapping soit le même pr ts les threads!!!
  //      -sig2code: on ajoute 1 indirection par ordinal de label pour diminuer les contention
  //      -code2sig: un simple atomicref d'array fera amplement l'affaire (faudra faire attention pr ne pas faire des allocs concurrentes...)

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

  private val sig2code = mutable.Map.empty[Signature, Code]
  private val code2sig = mutable.Map.empty[Code, Signature]
  private val sizeCache = mutable.Map.empty[Expr, Int]
  private val codeTpe = mutable.Map.empty[Code, Type]

  private var varIdCounter: Int = 0
  private val varId2Var = mutable.Map.empty[VarId, Variable]
  private val var2VarId = mutable.Map.empty[Variable, VarId]

  private val purityCache = mutable.Map.empty[Identifier, Boolean]
  private val codePurityCache = mutable.Map.empty[Code, Boolean]
  private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
  private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
  private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V
  private val visiting = mutable.Set.empty[Identifier]

  private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
  private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
  private val unitSig = Signature(Label.Lit(UnitLiteral()), Seq.empty)
  private val falseCode = codeOfSig(falseSig, BooleanType())
  private val trueCode = codeOfSig(trueSig, BooleanType())
  private val unitCode = codeOfSig(unitSig, UnitType())

  // TODO: fusionner les deux fns?
  def codeOfExpr(e: Expr)(using OEnv, InLambda): CodeRes = {
//    if (e.getType == BooleanType()) simplifiedDisjunction(pDisj(e).toSet)
//    else {
//      val sig = sigOfExpr(e)
//      codeOfSig(sig, e.getType)
//    }
    // TODO: fusionner les deux fns?
    sigOfExpr(e)
  }

  def negCodeOf(c: Code)(using OEnv): Code = {

    // TODO
    codeOfSig(mkNot(c), BooleanType())
    // ???
  } // codeOfSig(pNegNormal(c), BooleanType())

  // TODO: Pk ce truc est fait dans codeOf mais pas dans pDisj?
  // TODO: Et les assms???
  def simplifiedDisjunction(disj: Seq[Code])(using OEnv): Code = {
    codeOfSig(mkOr(disj), BooleanType())
  /*{
    assert(disj.forall(c => codeTpe(c) == BooleanType()))
    // TODO: Caching?
    val purity = fold(disj.map(codePurity).toSeq)
    val disj1 = disj.filter(_ != falseCode)
    if (disj1.isEmpty) falseCode
    else if (disj1.size == 1) disj1.head
    else if (purity.isPure && (disj1.contains(trueCode) || checkForContradiction(disj1))) trueCode
    else {
      val sig = Signature(Label.Or, disj1.toSeq.sorted)
      codeOfSig(sig, BooleanType())
    }
  }*/
  }

  // TODO: Puisque c'est un terminal, comment peut-il "contenir" un lambda? -> p.ex. par le moyen de if, assume, etc. tout ces trucs
  def needsBinding(terminal: Code, terminalHasLambdaDef: Boolean, occ: Occurrence)(using env: OEnv): Boolean = {
    code2sig(terminal) match {
      case Signature(Label.Lit(_) | Label.Var(_), _) => false
      case _ =>
        lazy val isPure = codePurity(terminal).isPure
        occ match {
          case Occurrence.Many => true
          case Occurrence.Zero if isPure => false
          case Occurrence.Once(_, inLambda) if isPure => inLambda && terminalHasLambdaDef
          case Occurrence.Once(inEnv, inLambda) =>
            // inEnv représente l'env. actif lors de l'occurrence de `terminal` dans le trou que l'on s'apprête à compléter.
            // S'il est différent de l'env ou `terminal` est introduit, alors on a besoin de let-bind, car inline
            // une expr impure après un PC est incorrect.
            (inEnv != env) || inLambda
          case Occurrence.Zero => true // Expr impure qui n'apparait pas dans le body; on ne peut pas l'éliminer, il faut donc le bind
        }
    }
  }

  // TODO: Quid simplif???
  def codeOfExprsBound(es: Seq[Expr], consTpe: Type)(cons: Seq[Code] => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), consTpe))

//  def codeOfExprsBound(es: Seq[Expr], consTpe: Type)(cons: Seq[Code] => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
//    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), consTpe))

  def codeOfExprsBound(e1: Expr, consTpe: Type)(cons: Code => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1), consTpe) { case Seq(c1) => cons(c1) }

  def codeOfExprsBound(e1: Expr, e2: Expr, consTpe: Type)(cons: (Code, Code) => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1, e2), consTpe) { case Seq(c1, c2) => cons(c1, c2) }

  def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, consTpe: Type)(cons: (Code, Code, Code) => Signature)(using env: OEnv, inLambda: InLambda): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), consTpe) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  // TODO: Dire que le nextEnv est appliqué pour le suivant (et pas pr le "current")
  // TODO: Quid simplif???
  def codeOfExprsBound(es: Seq[Expr])(cons: Seq[Code] => Code)(using env: OEnv, inLambda: InLambda): CodeRes = {
    given x_x: OEnv = sys.error("Carefully select env")

    // newEnv: l'environnement avec tous les let-bound des arguments (qui peuvent être elided)
    val (newEnv, codeRess) = es.foldLeft((env, Seq.empty[CodeRes])) {
      case ((env, codeResAcc), e) =>
        val codeResE = codeOfExpr(e)(using env)
        (codeResE.env, codeResAcc :+ codeResE)
//        /*
//        // TODO: Mais qu'est-ce que c'est que ce truc???
//        val bdg = idOfVariable(Variable.fresh("tmpArg", e.getType))
//        val newEnv0 = env.withLetBound(bdg, codeResE.terminal, canSubst = !isLambda(codeResE.terminal))
//        val newEnv1 = nextEnv(codeResE.terminal, newEnv0)
//        (newEnv1, codeResAcc :+ codeResE)
//        */
//        (nextEnv(codeResE.terminal, codeResE.env), codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess)(cons)(using newEnv)
  }

  // TODO: env?
  def combineCodeRes(codeRess: Seq[CodeRes])(cons: Seq[Code] => Code)(using env: OEnv, inLambda: InLambda): CodeRes = {
    val subterms = codeRess.map(_.terminal)
    val terminalContainsLam = codeRess.exists(_.terminalHasLambdaDef)
    val terminal = cons(subterms)
    val ctx = combinedCtx(terminal, terminalContainsLam)(codeRess.map(_.ctx))(_.incOccurrences(subterms :+ terminal))
    // TODO: Usages de terminal???
    CodeRes(terminal, terminalContainsLam, ctx, codeRess.foldLeft(Usages.empty)(_ ++ _.usages), env)
  }

//  def idCtx(using env: OEnv, inLambda: InLambda)(u: Usages, c: Code): (Usages, Code) = (u ++ Usages.of(c), c) // TODO: Ok?
  def idCtx(u: Usages, c: Code): (Usages, Code) = (u, c) // TODO: Ok?

  def combinedCtx(terminal: Code, terminalHasLam: Boolean)
                 (ctxs: Seq[(Usages, Code) => (Usages, Code)])
                 (incOccurrences: Usages => Usages) // TODO: Dire que resp. du caller d'incrémenter l'usg du terminal également
                 (using env: OEnv, inLambda: InLambda)
                 (u: Usages, c: Code): (Usages, Code) = {
    assert(!isLambda(terminal), "woot?? On n'est pas sensé construire un lambda avec cette fn!!!")
    val terminalOcc = u(terminal)
    // TODO: N'y a-t-il pas un risque qu'on compte les choses à double???
    if (needsBinding(terminal, terminalHasLam, terminalOcc)) {
      val tpe = codeTpe(terminal)
      val bdg = idOfVariable(Variable.fresh("bdg", tpe))
      val bound = codeOfSig(mkLet(bdg, terminal, c), tpe)
      val u2 = incOccurrences(u).setTo(terminal, Occurrence.Once(env, inLambda.v))
      foldCtxs(ctxs)(u2, bound)
    } else {
      val u2 = {
        if (terminalOcc.isZero) u
        else incOccurrences(u)
      }
      foldCtxs(ctxs)(u2, c)
    }
  }

  /*
  // TODO: env?
  def combinedCtx(terminal: Code, terminalHasLam: Boolean, subTerminals: Seq[Code])
                 (ctxs: Seq[(Usages, Code) => (Usages, Code)])
                 (u: Usages, c: Code)
                 (using env: OEnv, inLambda: InLambda): (Usages, Code) = {
    assert(!isLambda(terminal), "woot?? On n'est pas sensé construire un lambda avec cette fn!!!")
    assert(ctxs.size == subTerminals.size)
    val terminalOcc = u(terminal)
    if (needsBinding(terminal, terminalHasLam, terminalOcc)) {
      val tpe = codeTpe(terminal)
      val bdg = idOfVariable(Variable.fresh("bdg", tpe))
      val bound = codeOfSig(mkLet(bdg, terminal, c), tpe)
      val u2 = u.incOccurrence(subTerminals).setTo(terminal, Occurrence.Once(env, inLambda.v))
      foldCtxs(ctxs)(u2, bound)
    } else {
      val u2 = {
        if (terminalOcc.isZero) u
        else u.incOccurrence(subTerminals :+ terminal)
      }
      foldCtxs(ctxs)(u2, c)
    }
  }
  */

  def foldCtxs(ctxs: Seq[(Usages, Code) => (Usages, Code)])(u: Usages, c: Code): (Usages, Code) =
    ctxs.foldRight((u, c)) { case (ctx, (uAcc, cAcc)) => ctx(uAcc, cAcc) }

  // TODO: Quid simplif???
  // TODO: occurrences: terminal slmt???
  // TODO: occurrences: terminal slmt???
  // TODO: occurrences: terminal slmt???
  // TODO: occurrences: terminal slmt???
  // TODO: occurrences: terminal slmt???
  def sigOfExpr(e: Expr)(using env: OEnv, inLambda: InLambda): CodeRes = {
    val tpe = e.getType
    e match {
      case v: Variable =>
        val vId = idOfVariable(v)
        val c = substByLet(vId).getOrElse(codeOfVarId(vId))
        // TODO: termHasLambdaDef ok??? et si v est une ref. à une lambda???
        CodeRes.of(c, termHasLambdaDef = false)

      case l: Literal[_] => CodeRes.of(codeOfSig(mkLit(l), tpe), false)

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val envThen = rcond.env.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using envThen)
        val envEls = rcond.env.withCond(negCodeOf(rcond.terminal)(using rcond.env))
        val rels = codeOfExpr(els)(using envEls)

        // On ne hoist pas les let etc. des branches (donc on "self-plug")
        val cThenn = rthenn.selfPlugged
        val cEls = rels.selfPlugged
        val terminal = codeOfSig(mkIfExpr(rcond.terminal, cThenn, cEls), tpe)
        val termContainsLam = rcond.terminalHasLambdaDef || rthenn.terminalHasLambdaDef || rels.terminalHasLambdaDef
        // TODO: Env ok? En particulier pour les branches...
        locally {
          given x_x: OEnv = sys.error("Carefully select env")
          def incOcc(u: Usages): Usages = {
            u.incOccurrence(terminal)(using rcond.env)
              .incOccurrence(cThenn)(using envThen)
              .incOccurrence(cEls)(using envEls)
          }

          // val subctxs = Seq(rcond.ctx, idCtx(using envThen), idCtx(using envEls)) // TODO: Est-ce que cela est sensé????
          val ctx = combinedCtx(terminal, termContainsLam)(Seq(rcond.ctx))(incOcc)(using rcond.env)
          CodeRes(terminal, termContainsLam, ctx, rcond.usages ++ rthenn.usages ++ rels.usages ++ Usages.of(terminal), rcond.env)
        }

      case Lambda(params, body) =>
        val rbody = codeOfExpr(body)
        val cLam = codeOfSig(mkLambda(params.map(vd => idOfVariable(vd.toVariable)), rbody.selfPlugged), tpe)
        CodeRes.of(cLam, true)

      case Choose(res, pred) =>
        val rpred = codeOfExpr(pred)
        val cWicked = codeOfSig(mkWickedChoose(idOfVariable(res.toVariable), rpred.selfPlugged), tpe)
        CodeRes.of(cWicked, false)

      case Forall(params, pred) =>
        val rpred = codeOfExpr(pred)
        val cForall = codeOfSig(mkForall(params.map(vd => idOfVariable(vd.toVariable)), rpred.selfPlugged), tpe)
        CodeRes.of(cForall, false)

      // TODO: Inline lambda si occ == 1
      case Let(vd, e, body) =>
        val vId = idOfVariable(vd.toVariable)
        val re = codeOfExpr(e)
        val rb = codeOfExpr(body)(using re.env.withLetBound(vId, re.terminal, canSubst = !isLambda(re.terminal)))
        val ctx = (u: Usages, c: Code) => {
          val eOcc = u(re.terminal)
          // Pour `e`, on utilise l'environnement dans lequel il a été construit, donc re.env
          if (needsBinding(re.terminal, re.terminalHasLambdaDef, eOcc)(using re.env)) {
            val (u2, c2) = rb.ctx(u, c)
            val cLet = codeOfSig(mkLet(vId, re.terminal, c2), vd.getType)
            val u3 = u2.setTo(re.terminal, Occurrence.Once(re.env, inLambda.v))
            re.ctx(u3, cLet)
          } else {
            val (u2, c2) = rb.ctx(u, c)
            re.ctx(u2, c2)
          }
        }
        // TODO: terminalHasLambdaDef ok?
        CodeRes(rb.terminal, rb.terminalHasLambdaDef, ctx, /*re.usages ++ */rb.usages, rb.env)

        /*
        val ctx = (usgs: Usages) => (c: Code) => {
          val eOcc = usgs(re.terminal)
          // Pour `e`, on utilise l'environnement dans lequel il a été construit, donc re.env
          if (needsBinding(re.terminal, re.terminalHasLambdaDef, eOcc)(using re.env)) {
            // Pour re.ctx, puisque l'on bind `e`, on set que l'occurrence se passe exactement 1 fois
            val usgsCtxE = (usgs ++ rb.usages).setTo(re.terminal, Occurrence.Once(re.env, inLambda.v))
            // Pour rb.ctx en revanche, on laisse les occurrences tels quels
            val cLet = codeOfSig(mkLet(vId, re.terminal, rb.ctx(usgs)(c)), vd.getType)
            re.ctx(usgsCtxE)(cLet)
          } else {
            re.ctx(usgs ++ rb.usages)(rb.ctx(usgs)(c))
          }
        }
        // TODO: terminalHasLambdaDef ok?
        // TODO: Usgs ok? Si on elide le letdef, il ne faut pas qu'on compte re.usages...
        // TODO: -> rb.usages devrait etre ok? c'est usages de terminal!!!
        CodeRes(rb.terminal, rb.terminalHasLambdaDef, ctx, /*re.usages ++ */rb.usages, rb.env)
        */

      case e: (Assume | Assert | Require) =>
        val (pred, body, mkSig: ((Code, Code) => Signature)) = e match {
          case Assume(pred, body) => (pred, body, mkAssume)
          case Assert(pred, _, body) => (pred, body, mkAssert)
          case Require(pred, body) => (pred, body, mkRequire)
        }
        // TODO: Ok?
        val rpred = codeOfExpr(pred)
        val rbody = codeOfExpr(body)(using rpred.env.withCond(rpred.terminal))
        val ctx = foldCtxs(Seq(rpred.ctx, rbody.ctx))
        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, /*rpred.usages ++ */rbody.usages, rbody.env)
//        val ctx = (usgs: Usages) => (c: Code) => {
//          val cAssms = codeOfSig(mkSig(rpred.terminal, c), tpe)
//          rpred.ctx(usgs ++ rbody.usages)(rbody.ctx(usgs)(cAssms))
//        }
//        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, rbody.usages, rbody.env)

      case Decreases(measure, body) =>
        // TODO: Ok?
        val rmeasure = codeOfExpr(measure)
        val rbody = codeOfExpr(body)(using rmeasure.env)
        val ctx = foldCtxs(Seq(rmeasure.ctx, rbody.ctx))
        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, /*rmeasure.usages ++ */rbody.usages, rbody.env)
//        val ctx = (usgs: Usages) => (c: Code) => {
//          val cDecr = codeOfSig(mkDecreases(rmeasure.terminal, c), tpe)
//          rmeasure.ctx(usgs ++ rbody.usages)(rbody.ctx(usgs)(cDecr))
//        }
//        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, rbody.usages, rbody.env)

      case Ensuring(body, pred) =>
        // TODO: Ok?
        // TODO: Ok?
        // TODO: Ok?
        val rbody = codeOfExpr(body)
        val rpred = codeOfExpr(pred)(using rbody.env)
        val ctx = foldCtxs(Seq(rbody.ctx, rpred.ctx))
        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, /*rbody.usages ++ */rpred.usages, rbody.env)
//        val ctx = (usgs: Usages) => (c: Code) => {
//          val cReq = codeOfSig(mkEnsuring(c, rpred.terminal), tpe)
//          rbody.ctx(usgs ++ rpred.usages)(rpred.ctx(usgs)(cReq))
//        }
//        CodeRes(rbody.terminal, rbody.terminalHasLambdaDef, ctx, rbody.usages, rbody.env)

      case ADT(id, tps, args) => codeOfExprsBound(args, tpe)(mkADT(id, tps, _))
      case Tuple(args) => codeOfExprsBound(args, tpe)(mkTuple)
      case FunctionInvocation(id, tps, args) => codeOfExprsBound(args, tpe)(mkFunInvoc(id, tps, _))
      case Application(callee, args) => codeOfExprsBound(callee +: args, tpe) { case cCallee +: cArgs => mkApp(cCallee, cArgs) }
      case IsConstructor(e, id) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, tpe)(mkIsCtor(_, adt, id))
      case s @ ADTSelector(e, selector) =>
        val adt @ ADTType(_, _) = e.getType
        codeOfExprsBound(e, tpe)(mkADTSelector(_, adt, s.constructor, selector))

      // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
      // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
      //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
      //  une map ad-hoc qui contient ces infos...?
      case Annotated(e, flags) =>
        // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
        //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
        //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
        codeOfExprsBound(e, tpe)(mkAnnot(_, flags))

      // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
      case and @ And(_) =>
        val ands = unAnd(and)
        codeOfExpr(Not(Or(ands.map(Not.apply))))
      case or @ Or(_) =>
        // TODO: Pour le moment, pas d'ocbsl
        // TODO: Pour le moment, pas d'ocbsl
        // TODO: Pour le moment, pas d'ocbsl
        // TODO: checkForContradiction?
        ///// val cs = unOr(or).map(codeOfExpr).sorted.distinct
        // TODO: Move simplifyTopLvlSig
        ///// mkOr(cs)

        val disjs = unOr(or)
        // TODO: On pourrait juste hoist les exprs de head (-> il faudra donc modifier env et ctx retournés)
        val (envs :+ _, hasLamDef, usgs, cArgs) = disjs.foldLeft((Seq(env), false, Usages.empty, Seq.empty[Code])) {
          case ((envs, hasLamDefAcc, usgsAcc, cArgsAcc), e) =>
            given OEnv = envs.last
            val re = codeOfExpr(e)
            val rePlugged = re.selfPlugged
            val newEnv = re.env.withCond(negCodeOf(rePlugged))
            (envs :+ newEnv, hasLamDefAcc || re.terminalHasLambdaDef, usgsAcc ++ re.usages, cArgsAcc :+ rePlugged)
        }
        assert(envs.size == cArgs.size)

        val cOr = codeOfSig(mkOr(cArgs), tpe)
        // val subctx = envs.map(env => idCtx(using env)) // TODO: Est-ce que cela est sensé????
        def incOcc(u: Usages): Usages = {
          u.incOccurrence(cOr) // On doit incrémenter l'utilisation du terminal nous-même (dans env par défaut)
            .incOccurrences(cArgs.zip(envs))
        }
        val ctx = combinedCtx(cOr, hasLamDef)(Seq(idCtx))(incOcc) // TODO: sub ctx ok?
        // Remarque: on retourne l'env original car les PCs des ors ne sont pas retenues hors des disjunctions.
        // P.ex. dans val x = b1 || b2 || b3 il serait insensé d'avoir !b1 && !b2 && !b3 dans le env de x.
        // TODO: Ok ou bien CodeRes.of???
        CodeRes(cOr, hasLamDef, ctx, usgs ++ Usages.of(cOr), env)

        // CodeRes.of(cOr, hasLamDef)
        /*
        // TODO: Il y a surement mieux!!!
        val disjs = unOr(or)
        // TODO: On pourrait juste hoist les exprs de head
        val (newEnv, hasLamDef, usgs, cArgs) = disjs.foldLeft((env, false, Usages.empty, Seq.empty[Code])) {
          case ((env, hasLamDefAcc, usgsAcc, cArgsAcc), e) =>
            given OEnv = env
            val re = codeOfExpr(e)
            val rePlugged = re.selfPlugged
            val newEnv = re.env.withCond(negCodeOf(rePlugged))
            (newEnv, hasLamDefAcc || re.terminalHasLambdaDef, usgsAcc ++ re.usages, cArgsAcc :+ rePlugged)
        }
        val cOr = codeOfSig(mkOr(cArgs), tpe)
        // TODO: newEnv ok? <-- Non!!! Car les assms ne sont pas carried over!!!
        CodeRes(cOr, hasLamDef, _ => identity[Code], usgs, newEnv)
        */
        // TODO: Est-ce juste? On n'est pas sensé hoist des truc en dehors des Or!!! Cela introduit un PC après tout!!!
        /*
        codeOfExprsBound(unOr(or), tpe)(mkOr) { case (disj, env) =>
          given OEnv = env
          env.withCond(negCodeOf(disj))
        }
        */

      case Not(e) =>
        // TODO: Pour le moment, pas d'ocbsl
        // pNeg(e) // TODO: ? pk pas simplifyTopLvlSig?
        codeOfExprsBound(e, tpe)(mkNot)

      case Implies(e1, e2) => codeOfExpr(Or(Not(e1), e2))
      case Equals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkEquals)
      case LessThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessThan)
      case GreaterThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterThan)
      case LessEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessEquals)
      case GreaterEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterEquals)
      case UMinus(e) => codeOfExprsBound(e, tpe)(mkUMinus)
      case Plus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkPlus)
      case Minus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkMinus)
      case Times(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkTimes)
      case Division(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkDivision)
      case Remainder(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkRemainder)
      case Modulo(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkModulo)
      case BVNot(e) => codeOfExprsBound(e, tpe)(mkBVNot)
      case BVAnd(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAnd)
      case BVOr(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVOr)
      case BVXor(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVXor)
      case BVShiftLeft(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVShiftLeft)
      case BVAShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAShiftRight)
      case BVLShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVLShiftRight)
      case BVNarrowingCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVNarrowingCast(_, newTpe))
      case BVWideningCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVWideningCast(_, newTpe))
      case BVUnsignedToSigned(e) => codeOfExprsBound(e, tpe)(mkBVUnsignedToSigned)
      case BVSignedToUnsigned(e) => codeOfExprsBound(e, tpe)(mkBVSignedToUnsigned)
      case TupleSelect(e, index) => codeOfExprsBound(e, tpe)(mkTupleSelect(_, index))
      case FiniteSet(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteSet(_, base))
      case SetAdd(set, elem) => codeOfExprsBound(set, elem, tpe)(mkSetAdd)
      case ElementOfSet(elem, set) => codeOfExprsBound(elem, set, tpe)(mkElementOfSet)
      case SubsetOf(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSubsetOf)
      case SetIntersection(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetIntersection)
      case SetUnion(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetUnion)
      case SetDifference(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetDifference)
      case FiniteArray(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteArray(_, base))
      case LargeArray(elems, default, size, base) => ???
      case ArraySelect(array, index) => codeOfExprsBound(array, index, tpe)(mkArraySelect)
      case ArrayUpdated(array, index, v) => codeOfExprsBound(array, index, v, tpe)(mkArrayUpdated)
      case ArrayLength(array) => codeOfExprsBound(array, tpe)(mkArrayLength)

      case Error(ofTpe, descr) =>
        CodeRes.of(codeOfSig(mkError(ofTpe, descr), tpe), false)
      case NoTree(ofTpe) =>
        CodeRes.of(codeOfSig(mkNoTree(ofTpe), tpe), false)

      // TODO: Passer en revue la pureté: p.ex. si on est pas exhaustif, devrait-on retourner "assumeChecked"?
      case MatchExpr(scrut, cases) =>
        val rscrut = codeOfExpr(scrut)
        val (rcases, casesHasLamDef) = signatureOfCases(rscrut.terminal, scrut.getType, cases, Seq.empty, accHasLambdaDef = false)(using rscrut.env)
        // Ici, on fait qqchose de similaire au IfExpr
        val terminal = codeOfSig(mkMatchExpr(rscrut.terminal, rcases.map(_.mc)), tpe)
        val hasLam = rscrut.terminalHasLambdaDef || casesHasLamDef

        locally {
          given x_x: OEnv = sys.error("Carefully select env")
          def incOcc(u: Usages): Usages = {
            u.incOccurrence(terminal)(using rscrut.env)
              .incOccurrences(rcases.flatMap(rc => Seq((rc.mc.guard, rc.guardEnv), (rc.mc.rhs, rc.rhsEnv))))
          }
//          // TODO: Ok? Ca à l'air trop naif et stupide...
//          val subctxs = rscrut.ctx +: rcases.flatMap {
//            case SigOfMatchCaseResult(_, guardEnv, rhsEnv) =>
//              Seq(idCtx(using guardEnv), idCtx(using rhsEnv)) // TODO: Est-ce que cela est sensé????
//          }
          val ctx = combinedCtx(terminal, hasLam)(Seq(rscrut.ctx))(incOcc)(using rscrut.env)
          // TODO: rscrut.usages?
          CodeRes(terminal, hasLam, ctx, rcases.foldLeft(Usages.of(terminal)(using rscrut.env))(_ ++ _.usages) , rscrut.env)
        }

        /*
        val ctx = (usgs: Usages) => (c: Code) => {
          val termOcc = usgs(terminal)
          val usgsInc = usgs.incOccurrence(rscrut.terminal +: cCases.flatMap(mc => Seq(mc.guard, mc.rhs)), rscrut.env, inLambda)

          if (needsBinding(terminal, termContainsLam, termOcc)(using rscrut.env)) {
            val bdg = idOfVariable(Variable.fresh("matchBinding", tpe))
            val bound = codeOfSig(mkLet(bdg, terminal, c), tpe)
            rscrut.ctx(usgsInc)(bound)
          } else {
            rscrut.ctx(if (termOcc.isZero) usgs else usgsInc)(c)
          }
        }
        CodeRes(terminal, termContainsLam, ctx, rscrut.usages ++ casesUsgs, env)
        */

      case e =>
        println("computeSignature: Do not know how to handle "+e)
        ???
    }
  }

  def signatureOfPatternExpr(subScrut: Code, scrutTpe: Type, pat: Pattern)(using env: OEnv): (LabelledPattern, Seq[(VarId, Code)], Seq[Code]) = {
    val vBinder = idOfVariable(pat.binder.getOrElse(ValDef.fresh("dummyBinder", scrutTpe)).toVariable)
    val bdgs1 = Seq((vBinder, subScrut))
    pat match {
      case WildcardPattern(_) => (LabelledPattern.Wildcard(subScrut), bdgs1, Seq.empty)

      case ADTPattern(_, id, tps, subps) =>
        val adt = ADTType(id, tps)
        val tcons = getConstructor(id, tps)
        assert(tcons.fields.size == subps.size)
        val conds1 = {
          // Using `simplifySigTopLvl` here as it can reduce to `true` if this ADT is the only ctor
          val isCtorSig = simplifySigTopLvl(mkIsCtor(subScrut, adt, id), BooleanType())
          codeOfSig(isCtorSig, BooleanType())
        }
        val (labSubPats, bdgs2, conds2) = tcons.fields.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, Seq(conds1))) {
          // TODO: Annoté en dropvc?
          case ((labSubPatAcc, bdgsAcc, condsAcc), (fld, subpat)) =>
            val newScrut = codeOfSig(mkADTSelector(subScrut, adt, tcons, fld.id), fld.getType)
            // TODO: Env avec conds accumulées ok?
            val (labSubPat, newBdgs, newConds) = signatureOfPatternExpr(newScrut, fld.getType, subpat)(using env.withConds(condsAcc.toSet))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        (LabelledPattern.ADT(subScrut, id, tps, labSubPats), bdgs2, conds2)

      case TuplePattern(_, subps) =>
        val TupleType(bases) = scrutTpe
        assert(bases.size == subps.size)
        val (labSubPats, bdgs2, conds) = subps.zipWithIndex.foldLeft((Seq.empty[LabelledPattern], bdgs1, Seq.empty[Code])) {
          case ((labSubPatAcc, bdgsAcc, condsAcc), (subpat, i)) =>
            val newScrutTpe = bases(i)
            val newScrut = codeOfSig(mkTupleSelect(subScrut, i + 1), newScrutTpe)
            // TODO: Env avec conds accumulées ok?
            val (labSubPat, newBdgs, newConds) = signatureOfPatternExpr(newScrut, newScrutTpe, subpat)(using env.withConds(condsAcc.toSet))
            (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
        }
        (LabelledPattern.TuplePattern(subScrut, labSubPats), bdgs2, conds)

      case LiteralPattern(_, lit) => (LabelledPattern.Lit(subScrut ,lit), bdgs1, Seq.empty)

      case UnapplyPattern(_, recs, id, tps, subps) =>
        // TODO: !!!! Si on utilise codeOf, ne pas oublier d'utiliser le subst approprié !!!
        sys.error(s"Does not know how to handle $pat")
    }
  }

  case class SigOfMatchCaseResult(mc: LabMatchCase, guardEnv: OEnv, rhsEnv: OEnv, usages: Usages)

  def signatureOfCase(cScrut: Code, scrutTpe: Type, mc: MatchCase)(using env: OEnv, inLambda: InLambda): (SigOfMatchCaseResult, Seq[Code], Boolean) = {
    // patConds: sans le guard!
    val (labPat, bdgs, patConds) = signatureOfPatternExpr(cScrut, scrutTpe, mc.pattern)
    // TODO: canSubst?
    // TODO: !!! Si canSubst = false, il faudra faire un freshen d'identifiant p.ex. dans inlineLambda !!!
    val guardEnv = env.withLetBounds(bdgs, canSubst = true).withConds(patConds.toSet)
    // TODO: On pourrait conserver le ctx des guard pour le body? En gros, qu'on plug le body dans le ctx de guard
    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using guardEnv))
    val (cGuard, usgsGuard) = rguard.map(rg => (rg.selfPlugged, rg.usages)).getOrElse((trueCode, Usages.empty))
    val rhsEnv = guardEnv.withCond(cGuard)
    // Comme pour les ifs, on ne hoist rien des branches
    val rrhs = codeOfExpr(mc.rhs)(using rhsEnv)
    val labMc = LabMatchCase(labPat, cGuard, rrhs.selfPlugged)
    (SigOfMatchCaseResult(labMc, guardEnv, rhsEnv, usgsGuard ++ rrhs.usages), patConds :+ cGuard, rrhs.terminalHasLambdaDef)
  }

  def signatureOfCases(cScrut: Code, scrutTpe: Type, mcs: Seq[MatchCase], acc: Seq[SigOfMatchCaseResult], accHasLambdaDef: Boolean)
                      (using env: OEnv, inLambda: InLambda): (Seq[SigOfMatchCaseResult], Boolean) = {
    if (mcs.isEmpty) (acc, accHasLambdaDef)
    else {
      val (newMatchCase, caseConds, hasLambdaDef) = signatureOfCase(cScrut, scrutTpe, mcs.head)
      val negCaseConds = negatedConjunction(caseConds)
      signatureOfCases(cScrut, scrutTpe, mcs.tail, acc :+ newMatchCase, accHasLambdaDef || hasLambdaDef)(using env.withCond(negCaseConds))
    }
  }

  def checkForContradiction(disj: Set[Code])(using OEnv): Boolean = {
    if (disj.exists(c => !codePurity(c).isPure)) {
      return false
    }

    // TODO: Relativement different par rapport à l'orig
    val (pos, neg) = disj.foldLeft((Set.empty[Code], Set.empty[Code])) {
      case ((posAcc, negAcc), c) =>
        code2sig(c) match {
          case Signature(Label.Not, Seq(cc)) => (posAcc, negAcc + cc)
          case _ => (posAcc + c, negAcc)
        }
    }

    if (pos.intersect(neg).nonEmpty) true
    else {
      neg.exists { negC =>
        code2sig(negC) match {
          case Signature(Label.Or, negDisj) =>
            // TODO: Est-ce vrai? Quid si un meme code apparait dans un truc negatif?
            negDisj.forall(disj.contains)
          case _ => false
        }
      }
    }
  }

  // TODO: Ok?
  def pDisj(e: Expr)(using OEnv): Seq[Code] = {
    ???
//    assert(e.getType == BooleanType(), s"Got ${e.getType}")
//    sigOfExpr(e) match {
//      case Signature(Label.Or, children) => children // TODO: Flatten more?
//      case Signature(Label.Not, Seq(c)) => Seq(codeOfSig(pNegNormal(c), BooleanType())) // TODO: Ok?
//      case sig => Seq(codeOfSig(sig, BooleanType()))
//    }
  }

  // TODO: Voir si on peut pas faire qqchose pr eviter code dup avec pNegNormal
  // Signature de Not(child)
  def pNeg(child: Expr)(using OEnv): Signature = {

    ???
    /*
    // TODO: Où devrait-on mettre le caching? C'est appelé par computeSignature donc ça devrait faire l'affaire non?

    child match {
      case Not(e) => sigOfExpr(e) // TODO: Orig fait pDisj, mais pDisj et un computeSignature pour nous (du moins, pour le moment)
      // TODO: Les <= en > etc.
      case or @ Or(_) =>
        // Note: ors cannot be empty (by Or `require`)
        val ors0 = unOr(or)
        val ors1 = ors0.sortBy(sizeOf)
        // TODO: Ici, on fait un filter..distinct.sorted, ce que l'orig ne fait pas vraiment?
        val r = ors1.tail.flatMap(pDisj)
          .filter(_ != falseCode)
          .sorted.distinct
        if (r.isEmpty) pNeg(ors1.head) // TODO: Caching?
        else {
          // TODO: Ok?
          // TODO: Ressemble pas mal à simplifiedDisjunction
          val s = (pDisj(ors1.head) ++ r)
            .filter(_ != falseCode)
            .sorted.distinct
          val purity = fold(s.map(codePurity))
          if (purity.isPure && (s.contains(trueCode) || checkForContradiction(s.toSet))) falseSig
          else if (s.size == 1) pNegNormal(s.head)
          else mkNot(codeOfSig(mkOr(s), BooleanType()))
        }
      case _ =>
        // TODO: Ok?
        sigOfExpr(child) match {
          case Signature(Label.Lit(BooleanLiteral(b)), Seq()) => b2sig(!b)
          case sig => mkNot(codeOfSig(sig, BooleanType()))
        }
    }*/
  }

  // TODO: ok?
  // TODO: caching?
  // TODO: En gros la signature de Not(c)
  def pNegNormal(c: Code): Signature = {
    ???
//    assert(code2sig.contains(c))
//    code2sig(c) match {
//      case Signature(Label.Not, Seq(cc)) => code2sig(cc)
//      case Signature(_, _) => Signature(Label.Not, Seq(c)) // TODO: Ok?
//    }
  }

  def freshened(v: VarId): VarId = idOfVariable(varId2Var(v).freshen)

  def codeOfSig(sig: Signature, tpe: Type): Code = {
    sig2code.get(sig) match {
      case Some(c) =>
        assert(codeTpe(c) == tpe, s"${codeTpe(c)} != $tpe")
        c
      case None =>
        val newCode = Code.fromInt(sig2code.size)
        assert(!code2sig.contains(newCode))
        sig2code += sig -> newCode
        code2sig += newCode -> sig
        codeTpe += newCode -> tpe

        // TODO: Bouger ce truc dans CodePurity
        /*
        purity match {
          case Pure => codePurityCache += newCode -> true
          case Impure => codePurityCache += newCode -> false
          case Delayed(blockers) =>
            codeBlockedBy += newCode -> blockers
            for (blocker <- blockers) {
              val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
              blocking += blocker -> (blockedFns, blockedCodes + newCode)
            }
        }
        */
        newCode
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def implied(rhs: Code)(using env: OEnv): Boolean = {
    if (env.conditions.isEmpty) rhs == trueCode
    else {
      // TODO: Quid pureté de rhs???
      // TODO: Pourrait-on envisager de cache env.condition?
      // a ==> b === a && b = a
      val lhsConj = conjunct(env.conditions.toSeq) // TODO: Set to Seq ok?
      val rhsLhsConj = conjunct(Seq(lhsConj, rhs))
      rhsLhsConj == lhsConj
    }
  }

  // Is `c` an ADT with constructor `id`?
  //   Some(true) - Yes
  //   Some(false) - No
  //   None - Can't tell
  def isConstructor(c: Code, adt: ADTType, id: Identifier)(using OEnv): Option[Boolean] = {
    // TODO: What about purity?
    def codeIsCtor(ofId: Identifier): Code =
      codeOfSig(Signature(Label.IsConstructor(adt, ofId), Seq(c)), BooleanType())
    def codeNotCtor(ofId: Identifier): Code =
      negCodeOf(codeIsCtor(ofId))

    code2sig(c) match {
      case Signature(Label.ADT(id2, _), _) => Some(id == id2)
      case _ =>
        if (implied(codeIsCtor(id))) Some(true)
        else if (implied(codeNotCtor(id))) Some(false)
        else {
          val cons = getConstructor(id, adt.tps)
          val sort = cons.sort
          // All other constructors (excluding `id`) for the ADT
          val alts = (sort.constructors.toSet - cons).map(_.id)

          if (alts.exists(alt => implied(codeIsCtor(alt)))) Some(false)
          else if (alts.forall(alt => implied(codeNotCtor(alt)))) Some(true)
          else None
        }
    }
  }

  def idOfVariable(v: Variable): VarId = var2VarId.get(v) match {
    case Some(vId) => vId
    case None =>
      val vId = VarId.fromInt(varIdCounter)
      varIdCounter += 1
      var2VarId += v -> vId
      varId2Var += vId -> v
      vId
  }
  def varTpe(v: VarId): Type = varId2Var(v).tpe

  def conjunct(conj: Seq[Code])(using OEnv): Code = negCodeOf(negatedConjunction(conj))

  def negatedConjunction(conj: Seq[Code])(using OEnv): Code= {
    // TODO
    if (conj.size == 1) negCodeOf(conj.head)
    else codeOfSig(mkOr(conj.map(negCodeOf)), BooleanType())
    // TODO: Caching?
//    simplifiedDisjunction(conj.map(negCodeOf))
//    ???
  }

  def codeOfIntLit(lit: BigInt, tpe: Type): Code = codeOfSig(mkLit(intLitOfType(lit, tpe)), tpe)

  def intLitOfType(lit: BigInt, tpe: Type): Literal[_] = tpe match {
    case IntegerType() => IntegerLiteral(lit)
    case RealType() => FractionLiteral(lit, 1)
    case BVType(signed, size) =>
      // BVLiteral guards against signed=true and lit < 0, but not against lit not fitting
      // into the given bitwidth (it wrap-around)
      val (loIncl, hiExcl) = {
        if (signed) (-BigInt(2).pow(size-1), BigInt(2).pow(size-1))
        else (BigInt(0), BigInt(2).pow(size))
      }
      if (!(loIncl <= lit && lit < hiExcl)) {
        sys.error(s"$lit does not fit into $tpe  (with range [$loIncl, $hiExcl[)")
      }
      BVLiteral(signed, lit, size)
    case _ => sys.error(s"$tpe is not an integer-like type")
  }

  /*
  def simpForall(nbParams: Int, body: Code)(using subst: Subst): Signature = {
    def liftForall(es: Seq[Code]): Signature = {
      // TODO: Il faudra incrémenter les indexed vars des forall
      val (nbParamss, bodies) = es.map(c => code2sig(c) match {
        case Signature(Label.Forall(nbParams2), body2) => (nbParams2, ???) // TODO: Qqchose à faire par rapport aux indexed vars???
        case s => (0, s)
      }).unzip
      val allParams = nbParams + nbParamss.sum
      val combinedBody = ???
      if (allParams == nbParams) Signature(Label.Forall(nbParams), combinedBody)
      else simpForall(allParams, combinedBody)
    }

    code2sig(body) match {
      case Signature(Label.Forall(nbParams2), Seq(body2)) => simpForall(nbParams + nbParams2, body2)
      // TODO: On n'a pas de And ou Implies!!! On devrait pouvoir les "reconstruire"
      case Signature(Label.Or, disjs) => ???
      case _ => Signature(Label.Forall(nbParams), Seq(body))
    }
  }
  */

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class RevEnv(revLetDefs: Map[Code, VarId]) {
    def withLetBounds(vs: Seq[(VarId, Code)]): RevEnv =
      RevEnv(revLetDefs ++ vs.map { case (v, c) => c -> v }.toMap)

    def withLetBounds(v: VarId, c: Code): RevEnv =
      RevEnv(revLetDefs + (c -> v))
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty)
  }

  case class RevRes(expr: Expr, used: Set[VarId])

  def uncodeOf(c: Code)(using renv: RevEnv): RevRes = {
    renv.revLetDefs.get(c) match {
      case Some(vIx) =>
        return RevRes(varId2Var(vIx), Set(vIx))
      case None => ()
    }

    code2sig(c) match {
      case Signature(Label.Var(v), Seq()) => RevRes(varId2Var(v), Set(v))
      case Signature(Label.Lit(lit), Seq()) => RevRes(lit, Set.empty)
      case Signature(Label.Tuple, args) => recHelper(args)(Tuple.apply)
      case Signature(Label.ADT(id, tps), args) => recHelper(args)(ADT(id, tps, _))
      case Signature(Label.ADTSelector(_, _, sel), Seq(recv)) => recHelper(recv)(ADTSelector(_, sel))
      case Signature(Label.FunctionInvocation(id, tps), args) => recHelper(args)(FunctionInvocation(id, tps, _))
      case Signature(Label.Annotated(flags), Seq(e)) => recHelper(e)(Annotated(_, flags))
      case Signature(Label.IsConstructor(_, id), Seq(e)) => recHelper(e)(IsConstructor(_, id))
      case Signature(Label.Application, all@(callee +: args)) =>
        recHelper(all) { case callee +: args => Application(callee, args) }

      case Signature(Label.Let(v), Seq(cE, cBody)) =>
        val e = uncodeOf(cE)
        val body = uncodeOf(cBody)(using renv.withLetBounds(v, cE))
        RevRes(Let(new ValDef(varId2Var(v)), e.expr, body.expr), e.used ++ body.used)

      // TODO: Ok?
      case Signature(Label.Assume, Seq(pred, body)) => recHelper(pred, body)(Assume.apply)
      case Signature(Label.Assert, Seq(pred, body)) => recHelper(pred, body)(Assert(_, None, _))
      case Signature(Label.Require, Seq(pred, body)) => recHelper(pred, body)(Require.apply)
      case Signature(Label.Ensuring, Seq(body, pred)) =>
        recHelper(body, pred) { case (body, pred: Lambda) => Ensuring(body, pred) }
      case Signature(Label.Decreases, Seq(measure, body)) => recHelper(measure, body)(Decreases.apply)

      case Signature(Label.IfExpr, Seq(cond, thn, els)) => recHelper(cond, thn, els)(IfExpr.apply)
      case Signature(Label.Lambda(params), Seq(body)) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        recHelper(body)(Lambda(vds, _))
      case Signature(Label.Choose(v), Seq(pred)) => recHelper(pred)(Choose(new ValDef(varId2Var(v)), _))
      case Signature(Label.Forall(params), Seq(pred)) =>
        val vds = params.map(v => new ValDef(varId2Var(v)))
        recHelper(pred)(Forall(vds, _))

      case Signature(Label.Or, args) => recHelper(args)(Or.apply)
      // TODO: Pour un Not(Or(...)), transformer en And(...)
      case Signature(Label.Not, Seq(c)) => recHelper(c)(Not.apply)
      case Signature(Label.Equals, Seq(c1, c2)) => recHelper(c1, c2)(Equals.apply)
      case Signature(Label.LessThan, Seq(c1, c2)) => recHelper(c1, c2)(LessThan.apply)
      case Signature(Label.GreaterThan, Seq(c1, c2)) => recHelper(c1, c2)(GreaterThan.apply)
      case Signature(Label.LessEquals, Seq(c1, c2)) => recHelper(c1, c2)(LessEquals.apply)
      case Signature(Label.GreaterEquals, Seq(c1, c2)) => recHelper(c1, c2)(GreaterEquals.apply)
      case Signature(Label.UMinus, Seq(c)) => recHelper(c)(UMinus.apply)
      case Signature(Label.Plus, Seq(c1, c2)) => recHelper(c1, c2)(Plus.apply)
      case Signature(Label.Minus, Seq(c1, c2)) => recHelper(c1, c2)(Minus.apply)
      case Signature(Label.Times, Seq(c1, c2)) => recHelper(c1, c2)(Times.apply)
      case Signature(Label.Division, Seq(c1, c2)) => recHelper(c1, c2)(Division.apply)
      case Signature(Label.Remainder, Seq(c1, c2)) => recHelper(c1, c2)(Remainder.apply)
      case Signature(Label.Modulo, Seq(c1, c2)) => recHelper(c1, c2)(Modulo.apply)
      case Signature(Label.BVNot, Seq(c)) => recHelper(c)(BVNot.apply)
      case Signature(Label.BVAnd, Seq(c1, c2)) => recHelper(c1, c2)(BVAnd.apply)
      case Signature(Label.BVOr, Seq(c1, c2)) => recHelper(c1, c2)(BVOr.apply)
      case Signature(Label.BVXor, Seq(c1, c2)) => recHelper(c1, c2)(BVXor.apply)
      case Signature(Label.BVShiftLeft, Seq(c1, c2)) => recHelper(c1, c2)(BVShiftLeft.apply)
      case Signature(Label.BVAShiftRight, Seq(c1, c2)) => recHelper(c1, c2)(BVAShiftRight.apply)
      case Signature(Label.BVLShiftRight, Seq(c1, c2)) => recHelper(c1, c2)(BVLShiftRight.apply)
      case Signature(Label.BVNarrowingCast(newType), Seq(c)) => recHelper(c)(BVNarrowingCast(_, newType))
      case Signature(Label.BVWideningCast(newType), Seq(c)) => recHelper(c)(BVWideningCast(_, newType))
      case Signature(Label.BVUnsignedToSigned, Seq(c)) => recHelper(c)(BVUnsignedToSigned.apply)
      case Signature(Label.BVSignedToUnsigned, Seq(c)) => recHelper(c)(BVSignedToUnsigned.apply)
      case Signature(Label.TupleSelect(index), Seq(c)) => recHelper(c)(TupleSelect(_, index))

      case Signature(Label.FiniteSet(base), args) => recHelper(args)(FiniteSet(_, base))
      case Signature(Label.SetAdd, Seq(set, elem)) => recHelper(set, elem)(SetAdd.apply)
      case Signature(Label.ElementOfSet, Seq(elem, set)) => recHelper(elem, set)(ElementOfSet.apply)
      case Signature(Label.SubsetOf, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SubsetOf.apply)
      case Signature(Label.SetIntersection, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetIntersection.apply)
      case Signature(Label.SetUnion, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetUnion.apply)
      case Signature(Label.SetDifference, Seq(lhs, rhs)) => recHelper(lhs, rhs)(SetDifference.apply)

      case Signature(Label.FiniteArray(base), args) => recHelper(args)(FiniteArray(_, base))
      case Signature(Label.LargeArray(elemsIndices, base), all@(elems :+ default :+ size)) =>
        recHelper(all) { case elems :+ default :+ size =>
          LargeArray(elemsIndices.zip(elems).toMap, default, size, base)
        }
      case Signature(Label.ArraySelect, Seq(arr, i)) => recHelper(arr, i)(ArraySelect.apply)
      case Signature(Label.ArrayUpdated, Seq(arr, i, v)) => recHelper(arr, i, v)(ArrayUpdated.apply)
      case Signature(Label.ArrayLength, Seq(arr)) => recHelper(arr)(ArrayLength.apply)

      case Signature(Label.Error(tpe, descr), Seq()) => RevRes(Error(tpe, descr), Set.empty)
      case Signature(Label.NoTree(tpe), Seq()) => RevRes(NoTree(tpe), Set.empty)

      case Signature(Label.MatchExpr(pats), cScrut +: cGuardRhs) =>
        assert(2 * pats.size == cGuardRhs.size)

        def convertPattern(pat: LabelledPattern, vds: Map[Code, ValDef]): Pattern = {
          val bdg = vds.get(pat.scrut)
          pat match {
            case LabelledPattern.Wildcard(_) => WildcardPattern(bdg)
            case LabelledPattern.ADT(_, id, tps, sub) => ADTPattern(bdg, id, tps, sub.map(convertPattern(_, vds)))
            case LabelledPattern.TuplePattern(_, sub) => TuplePattern(bdg, sub.map(convertPattern(_, vds)))
            case LabelledPattern.Lit(_, lit) => LiteralPattern(bdg, lit)
            case LabelledPattern.Unapply(_, recs, id, tps, sub) => ???
          }
        }

        def uncodeOfCase(pat: LabelledPattern, cGuard: Code, cRhs: Code): (Pattern, RevRes, RevRes) = {
          val allPats = pat.allPatterns
          val scrutBdgs = allPats.zipWithIndex.map {
            case (pat, i) =>
              val vId = idOfVariable(Variable.fresh(s"bdg$i", codeTpe(pat.scrut)))
              vId -> pat.scrut
          }
          val newRenv = renv.withLetBounds(scrutBdgs)
          val guard = uncodeOf(cGuard)(using newRenv)
          val rhs = uncodeOf(cRhs)(using newRenv)
          // On retire les scrut. binding qui sont inutiles.
          val scrutVds = scrutBdgs.filter { case (v, _) => guard.used(v) || rhs.used(v) }
            .map { case (v, c) =>
              val vd = new ValDef(varId2Var(v))
              c -> vd
            }.toMap
          (convertPattern(pat, scrutVds), guard, rhs)
        }
        val (guards, rhss) = cGuardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val scrut = uncodeOf(cScrut)
        val (cases, used) = pats.zip(guards).zip(rhss).foldLeft((Seq.empty[MatchCase], scrut.used)) {
          case ((accCases, accUsed), ((labPat, cGuard), cRhs)) =>
            val (pat, guard, rhs) = uncodeOfCase(labPat, cGuard, cRhs)
            val cse = MatchCase(pat, if (guard.expr == BooleanLiteral(true)) None else Some(guard.expr), rhs.expr)
            (accCases :+ cse, accUsed ++ guard.used ++ rhs.used)
        }
        RevRes(MatchExpr(scrut.expr, cases), used)

      case sig =>
        sys.error(s"uncodeOf: what is this: $sig")
    }
  }

  def recHelper(args: Seq[Code])(recons: Seq[Expr] => Expr)(using RevEnv): RevRes = {
    val rargs = args.map(uncodeOf)
    RevRes(recons(rargs.map(_.expr)), rargs.flatMap(_.used).toSet)
  }
  def recHelper(c1: Code)(recons: Expr => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1)) { case Seq(e1) => recons(e1) }
  def recHelper(c1: Code, c2: Code)(recons: (Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2)) { case Seq(e1, e2) => recons(e1, e2) }
  def recHelper(c1: Code, c2: Code, c3: Code)(recons: (Expr, Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2, c3)) { case Seq(e1, e2, e3) => recons(e1, e2, e3) }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def b2c(b: Boolean): Code = if (b) trueCode else falseCode
  def b2sig(b: Boolean): Signature = if (b) trueSig else falseSig

  val assmChkPurity: Purity = if (opts.assumeChecked) Pure else Impure

  def unAnd(e: Expr): Seq[Expr] = e match {
    case And(es) => es.flatMap(unAnd)
    case e => Seq(e)
  }

  def unOr(e: Expr): Seq[Expr] = e match {
    case Or(es) => es.flatMap(unOr)
    case e => Seq(e)
  }

  def sizeOf(e: Expr): Int = sizeCache.getOrElseUpdate(e, exprOps.formulaSize(e))

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def fnPurity(fn: Identifier): Purity = {
    def resolvedPurity(isPure: Boolean): Unit = {
      purityCache += fn -> isPure
      if (blocking.contains(fn)) {
        val (blockedFns, blockedCodes) = blocking.remove(fn).get
        for (blockedFn <- blockedFns) {
          assert(fnBlockedBy.contains(blockedFn))
          assert(fnBlockedBy(blockedFn) == Set(fn))
          fnBlockedBy -= blockedFn
          purityCache += blockedFn -> isPure
        }
        for (blockedCode <- blockedCodes) {
          assert(codeBlockedBy.contains(blockedCode))
          assert(codeBlockedBy(blockedCode) == Set(fn))
          codeBlockedBy -= blockedCode
          codePurityCache += blockedCode -> isPure
        }
      }
    }
    def addToBlocked(blockers: Set[Identifier]): Unit = {
      assert(!blockers.contains(fn))
      // On s'ajoute à la liste des bloqués
      fnBlockedBy += fn -> blockers
      for (blocker <- blockers) {
        val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
        blocking += blocker -> (blockedFns + fn, blockedCodes)
      }

      // On upd. les bloqués pour qu'ils pointent vers ceux qui nous bloquent, et pas nous.
      val (blockedFnsByThisFn, blockedCodeByThisCode) = blocking.remove(fn).getOrElse((Set.empty, Set.empty))
      for (blockedFn <- blockedFnsByThisFn) {
        assert(fnBlockedBy.contains(blockedFn))
        val upd = fnBlockedBy(blockedFn) - fn ++ blockers
        fnBlockedBy += blockedFn -> upd
      }
      for (blockedCode <- blockedCodeByThisCode) {
        assert(codeBlockedBy.contains(blockedCode))
        val upd = codeBlockedBy(blockedCode) - fn ++ blockers
        codeBlockedBy += blockedCode -> upd
      }
    }
    if (visiting.contains(fn)) {
      if (!opts.assumeChecked) Impure
      else Delayed(Set(fn))
    } else {
      purityCache.get(fn) match {
        case Some(true) => Pure
        case Some(false) => Impure
        case None =>
          // TODO: Quid condition venant du simplifier (s'il y en as???)?
          // TODO: Différencier:
          //    -outer assms et local assms
          //    -outer open bound et local open bound
          given OEnv = OEnv.empty
          given InLambda = InLambda(false)
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val res = codePurity(codeOfExpr(getFunction(fn).fullBody).selfPlugged)
          visiting -= fn
          res match {
            case Pure =>
              resolvedPurity(isPure = true)
              Pure
            case Impure =>
              resolvedPurity(isPure = false)
              Impure
            case Delayed(blockers0) =>
              assert(blockers0.nonEmpty)
              assert(opts.assumeChecked)
              assert(!fnBlockedBy.contains(fn))
              val blockersWoCurr = blockers0 - fn

              if (blockers0.contains(fn)) {
                assert(blocking.contains(fn))
                if (blockersWoCurr.isEmpty) {
                  resolvedPurity(isPure = true)
                  Pure
                } else {
                  addToBlocked(blockersWoCurr)
                  Delayed(blockersWoCurr)
                }
              } else {
                assert(!blocking.contains(fn))
                addToBlocked(blockers0)
                Delayed(blockers0)
              }
          }
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Ordre ok???
  // TODO: Ordre ok???
  // TODO: Ordre ok???
  def collectPatternConds(pat: LabelledPattern, recursive: Boolean)(using env: OEnv): Seq[Code] = pat match {
    case LabelledPattern.Wildcard(_) => Seq.empty
    case LabelledPattern.ADT(scrut, id, tps, subps) =>
      val adt = ADTType(id, tps)
      val tcons = getConstructor(id, tps)
      assert(tcons.fields.size == subps.size)
      // Using `simplifySigTopLvl` here as it can reduce to `true` if this ADT is the only ctor
      val isCtorSig = simplifySigTopLvl(mkIsCtor(scrut, adt, id), BooleanType())
      val cond = codeOfSig(isCtorSig, BooleanType())
      val subconds = {
        // TODO: env with cond ok?
        if (recursive)
          subps.flatMap(collectPatternConds(_, true)(using env.withCond(cond)))
        else Seq.empty
      }
      cond +: subconds
    case LabelledPattern.TuplePattern(_, subps) =>
      if (recursive) subps.flatMap(collectPatternConds(_, true))
      else Seq.empty
    case LabelledPattern.Lit(_, _) => Seq.empty
    case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
      sys.error(s"Does not know how to handle $pat")
  }

  def isLambda(c: Code): Boolean = code2sig(c) match {
    case Signature(Label.Lambda(_), _) => true
    case _ => false
  }

  // TODO: Dire que dans le graphe, cela equivaut a update les references selon repl.
  //  En particulier on ne duplique pas ("freshen locals") les let, lambda, forall, choose, etc.!!!
  def replaceIn(c: Code, repl: Map[Code, Code]): Code = {
    assert(repl.forall { case (old, nw) => codeTpe(old) == codeTpe(nw) })
    repl.getOrElse(c, {
      val Signature(lab, children) = code2sig(c)
      val replChildren = children.map(replaceIn(_, repl))
      val newSig = Signature(lab, replChildren)
      codeOfSig(newSig, codeTpe(c))
    })
  }

  def replaceIn(pat: LabelledPattern, repl: Map[Code, Code]): LabelledPattern = {
    val newScrut = replaceIn(pat.scrut, repl)
    pat match {
      case LabelledPattern.Wildcard(_) => LabelledPattern.Wildcard(newScrut)
      case LabelledPattern.ADT(_, id, tps, subps) =>
        LabelledPattern.ADT(newScrut, id, tps, subps.map(replaceIn(_, repl)))
      case LabelledPattern.TuplePattern(_, subps) =>
        LabelledPattern.TuplePattern(newScrut, subps.map(replaceIn(_, repl)))
      case LabelledPattern.Lit(_, lit) => LabelledPattern.Lit(newScrut, lit)
      case LabelledPattern.Unapply(_, recs, id, tps, subps) =>
        sys.error(s"Does not know how to handle $pat")
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def codeOfVarId(v: VarId): Code = codeOfSig(mkVar(v), varTpe(v))

  private val sigPurity = new SigPurity

  def codePurity(c: Code)(using env: OEnv): Purity = sigPurity.codePurity(c)
  def sigPurity(sig: Signature)(using env: OEnv): Purity = sigPurity.sigPurity(sig)

//  private val topLvlSigSimp = new TopLevelSigSimplifier

  // TODO
  def simplifySigTopLvl(sig: Signature, tpe: Type)(using OEnv): Signature = sig // topLvlSigSimp.transform(sig, tpe, Map.empty, ())

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  def inlineLetBoundLambda(lam: VarId, in: Code)(using env: OEnv): Code = {
    val (cLam, _) = env.letDef.getOrElse(lam, sys.error("Treachery!!! Lambda not in env!!!"))
    val lamVarIdCode = codeOfVarId(lam)
    val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam)

    class InlineWrapperImpl extends CodeTransformer(depthLimit = None) {
      override type Extra = Unit

      // TODO: Ok par rapport à repl + let-bound canSubst truc?
      override def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Unit)(using env: OEnv): Signature = sig match {
        case Signature(Label.Application, `lamVarIdCode` +: args) =>
          assert(params.size == args.size)
          code2sig(inlineLambda(params.zip(args), body))
        case _ => super.transformImpl(sig, tpe, repl, ())
      }
    }

    (new InlineWrapperImpl).transformImpl(in, Map.empty, ())
  }

  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: Cette histoire de assume(...) en début de lambda???
  // TODO: remarque sur subst dans l'ordre (repr. l'inlining d'argument)
  def inlineLambda(argsSubst: Seq[(VarId, Code)], body: Code)(using env: OEnv): Code = {
    // Essentiellement un freshener + simplifySigTopLvl a chaque step
    class InlinerImpl extends CodeTransformer(depthLimit = None) {
      override type Extra = Unit

      override def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Unit)(using env: OEnv): Signature = sig match {
        case Signature(Label.Let(v), Seq(e, b)) =>
          val re = transform(e, repl, ())
          val freshV = freshened(v)
          val newEnv = env.withLetBound(freshV, re, canSubst = !isLambda(re))
          val rb = transformImpl(b, repl + (codeOfVarId(v) -> codeOfVarId(freshV)), ())(using newEnv)
          simplifySigTopLvl(mkLet(freshV, re, rb), tpe)

        case Signature(Label.Lambda(params), Seq(body)) =>
          val freshParams = params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }
          val rbody = transform(body, repl ++ freshParamsRepl, ())
          simplifySigTopLvl(mkLambda(freshParams.map(_._2), rbody), tpe)

        case Signature(Label.Forall(params), Seq(pred)) =>
          val freshParams = params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }
          val rpred = transform(pred, repl ++ freshParamsRepl, ())
          simplifySigTopLvl(mkForall(freshParams.map(_._2), rpred), tpe)

        case Signature(Label.Choose(v), Seq(pred)) =>
          val freshV = freshened(v)
          val rpred = transform(pred, repl + (codeOfVarId(v) -> codeOfVarId(freshV)), ())
          simplifySigTopLvl(mkWickedChoose(freshV, rpred), tpe)

        // Remarque: pas de freshening à faire pour Match parce qu'il n'y a pas de binding à proprement parler

        case Signature(_, _) =>
          val rsig = super.transformImpl(sig, tpe, repl, ())
          simplifySigTopLvl(rsig, tpe)
      }
    }

    // TODO: Remarque: inline une lambda peut donner lieu a une expr impure...
    // TODO: Pureté?
    val bodyTpe = codeTpe(body)
    val freshVars = argsSubst.map { case (v, _) => v -> freshened(v) }
    val freshVarsMap = freshVars.toMap
    val argsSubstMap = argsSubst.toMap
    // Bind the argument to fresh variables
    val initEnvBindings = freshVars.map {
      case (oldV, newV) => newV -> argsSubstMap(oldV)
    }
    val initEnv = env.withLetBounds(initEnvBindings)((_, c) => !isLambda(c))
    // Map to replace all occurrences of the old parameter with the fresh bindings variables.
    // TODO: Ok ça va se faire replace, mais ensuite??? Il n'y a pas la subst de letbind qui se fait!!!!
    //    -> Devrait être ok (CodeTransformer se charge)
    val initRepl = freshVars.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
    val inlined = (new InlinerImpl).transform(body, initRepl, ())(using initEnv)

    assert(codeTpe(inlined) == bodyTpe)
    argsSubst.foldRight(inlined) {
      case ((oldV, arg), rest) =>
        val newV = freshVarsMap(oldV)
        codeOfSig(mkLet(newV, arg, rest), bodyTpe)
    }
  }
  */

  def substByLet(v: VarId)(using env: OEnv): Option[Code] = env.letDef.get(v).filter(_._2).map(_._1)

  /*
  class TopLevelSigSimplifier extends CodeTransformer(depthLimit = Some(1)) {
    override type Extra = Unit

    override def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Unit)(using env: OEnv): Signature = {
      lazy val zero = codeOfIntLit(0, tpe)
      lazy val one = codeOfIntLit(1, tpe)
      lazy val zeroSig = code2sig(zero)
      lazy val oneSig = code2sig(one)

      sig match {
        case Signature(Label.Assume, Seq(pred, body)) =>
          if (pred == trueCode) code2sig(body)
          else sig

        case Signature(Label.Assert, Seq(pred, body)) =>
          if (pred == trueCode) code2sig(body)
          else sig

        case Signature(Label.Require, Seq(pred, body)) =>
          if (pred == trueCode) code2sig(body)
          else sig

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          code2sig(pred) match {
            case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => code2sig(body)
            case _ => sig
          }

        case Signature(Label.Let(v), Seq(_, _)) =>
          val rsig@Signature(Label.Let(`v`), Seq(re, rbody)) = super.transformImpl(sig, tpe, repl, ())
          if (rbody == unitCode) code2sig(re)
          else rsig

        case Signature(Label.IfExpr, Seq(cond, thenn, elze)) =>
          val pCond = codePurity(cond)
          val pThen = codePurity(thenn)
          val pElse = codePurity(elze)

          // Note: on check la purity de `else` parce que c'est elle qu'on va dropper
          // TODO: On peut faire des trucs comme ifExpr
          val fstTry: Option[Signature] = {
            if (pCond.isPure) {
              if (pElse.isPure && cond == trueCode) Some(code2sig(thenn))
              else if (pThen.isPure && cond == falseCode) Some(code2sig(elze))
              else if (thenn == elze) {
                assert(pThen == pElse)
                Some(code2sig(thenn))
              }
              else None
            } else None
          }

          def sndTry = (code2sig(thenn), code2sig(elze)) match {
            case (Signature(Label.IfExpr, Seq(cond2, thenn2, elze2)), _) if elze == elze2 =>
              val combinedCond = conjunct(Seq(cond, cond2))
              val c2 = codeOfSig(mkIfExpr(combinedCond, thenn2, elze2), tpe)
              val c3 = withIncreaseDepth(1)(transform(c2, repl, ()))
              code2sig(c3)
            case (_, Signature(Label.IfExpr, Seq(cond2, thenn2, elze2))) if thenn == thenn2 =>
              val combinedCond = simplifiedDisjunction(Seq(cond, cond2))
              val c2 = codeOfSig(mkIfExpr(combinedCond, thenn2, elze2), tpe)
              val c3 = withIncreaseDepth(1)(transform(c2, repl, ()))
              code2sig(c3)
            case _ => sig
          }

          fstTry.getOrElse(sndTry)

        case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
          val purity = codePurity(e)
          isConstructor(e, adt, id) match {
            case Some(b) if purity.isPure => b2sig(b)
            case Some(b) =>
              // TODO: On peut retirer ces bindings, car on le fait (ou fera) déjà
              val v = idOfVariable(Variable.fresh("tmp", codeTpe(e)))
              Signature(Label.Let(v), Seq(e, b2c(b))) // TODO: !!! on ne respecte pas cette histoire de hoisting !!!
            case None => sig
          }

        case Signature(Label.ADTSelector(adt, ctor, sel), Seq(e)) =>
          code2sig(e) match {
            // TODO: A-t-on de toute façon id == ctor.id ?
            // TODO: On peut retirer ces bindings, car on le fait (ou fera) déjà
            case Signature(Label.ADT(id, _), args) =>
              assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
              val index = ctor.definition.selectorID2Index(sel)
              // Les args qui ne sont pas pures doivent être let-bound
              val toBeBound = args.zipWithIndex.filter { case (c, i) => i != index && !codePurity(c).isPure }.map(_._1)
              // Le résultat de la selection
              val selRes = args(index)
              // TODO: En aura-t-on besoin? Si on bind tout avant avec un let, cela devrait faire l'affaire non?
              val resWithBdgs = toBeBound.foldRight(selRes) {
                case (arg, rest) =>
                  val v = idOfVariable(Variable.fresh("tmp", codeTpe(arg)))
                  codeOfSig(mkLet(v, arg, rest), tpe)
              }
              code2sig(resWithBdgs)

            // TODO: Egalement à faire dans d'autre cas
            // TODO: Egalement à faire dans d'autre cas
            // TODO: Egalement à faire dans d'autre cas
            // TODO: Quid autre expression qui peuvent bénéficier de ce hoisting? P.ex. Assume? Même si un peu plus délicat...
            // Turn a (lets vs = ... in recv).sel to a lets vs = ... in adt.sel
            case Signature(Label.Let(v), Seq(defs, recv)) if codePurity(defs).isPure => code2sig(recv) match {
              case Signature(Label.ADT(_, _), _) =>
                val cSel = codeOfSig(mkADTSelector(recv, adt, ctor, sel), tpe)
                val cSelSimp = withIncreaseDepth(1)(transform(cSel, repl, extra))
                mkLet(v, defs, cSelSimp)
              case _ => sig
            }

            case _ => sig
          }

        case Signature(Label.ADT(id, tps), args) =>
          // Simplification de ADT(base.fld1, base.fld2, etc.) en base si base est de meme nature que l'adt construite
          val ctor: TypedADTConstructor = getConstructor(id, tps)
          val bases: Seq[Code] = ctor.fields.zip(args.map(code2sig)).collect {
            case (vd, Signature(Label.ADTSelector(_, ctor2, sel), Seq(base)))
              if vd.id == sel && ctor == ctor2 => base
          }
          bases match {
            case base +: basesRest
              // TODO: v v v v v oui, c'est pour ça qu'il faut tout bind v v v v v
              // TODO: N'y a-t-il pas un risque de code duplication??? Ou pourrait-on gérer ce prob. lorsque l'on fera le "uncodeOf"???
              // TODO: Pas seulement ça, mais on risque de dupliquer "a tort" base non (problematique si impure)???
              // TODO: Orig fait e.getType == adt.getType, mais nous on fait ctor == ctor2, est-ce que ça va aussi?
              if bases.size == args.size &&
                basesRest.forall(_ == base) &&
                isConstructor(base, ADTType(id, tps), id) == Some(true) =>
              // Comme pour ADTSelector, les args qui ne sont pas pures doivent être let-bound
              val toBeBound = basesRest.filter(c => !codePurity(c).isPure)
              // On bind toBeBound et on retourne `base` (en foldant dessus)
              // let _ = toBeBound in base
              val resWithBdgs = toBeBound.foldRight(base) {
                case (arg, rest) =>
                  val v = idOfVariable(Variable.fresh("tmp", codeTpe(arg)))
                  codeOfSig(mkLet(v, arg, rest), tpe)
              }
              code2sig(resWithBdgs)
            case _ => sig
          }

        case Signature(Label.TupleSelect(ii), Seq(e)) =>
          val i = ii - 1
          code2sig(e) match {
            case Signature(Label.Tuple, args) =>
              // Comme pour ADTSelector, les args qui ne sont pas pures doivent être let-bound
              val toBeBound = args.zipWithIndex.filter { case (c, j) => i != j && !codePurity(c).isPure }.map(_._1)
              // let _ = toBeBound in args(i)
              val resWithBdgs = toBeBound.foldRight(args(i)) {
                case (arg, rest) =>
                  val v = idOfVariable(Variable.fresh("tmp", codeTpe(arg)))
                  codeOfSig(mkLet(v, arg, rest), tpe)
              }
              code2sig(resWithBdgs)
            case _ => sig
          }

        case Signature(Label.Application, callee +: args) =>
          // TODO: On suppose que si callee est originellement let-bound, alors son occurrence est de 1 (pr éviter explosion d'inlining)
          code2sig(callee) match {
            case Signature(Label.Lambda(params), Seq(body)) =>
              assert(args.size == params.size)
              val inlined = inlineLambda(params.zip(args), body)
              code2sig(inlined)
            case _ => sig
          }

        case Signature(Label.Equals | Label.GreaterEquals | Label.LessEquals, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); trueSig }
          else sig

        case Signature(Label.LessThan | Label.GreaterThan, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); falseSig }
          else sig

        case Signature(Label.UMinus, Seq(e)) =>
          code2sig(e) match {
            case Signature(Label.UMinus, Seq(e2)) => code2sig(e2)
            case _ => sig
          }

        case Signature(Label.Plus, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == zero) { assert(p1.isPure); code2sig(e2) }
          else if (e2 == zero) { assert(p2.isPure); code2sig(e1) }
          else sig

        case Signature(Label.Minus, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); zeroSig }
          else sig

        case Signature(Label.Times, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); zeroSig }
          else if (e1 == one) { assert(p1.isPure); code2sig(e2) }
          else if (e2 == one) { assert(p2.isPure); code2sig(e1) }
          else sig

        case Signature(Label.Division | Label.Remainder | Label.Modulo, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (opts.assumeChecked && e2 != zero && e1 == zero && p2.isPure) { assert(p1.isPure); zeroSig }
          else if (opts.assumeChecked && e2 != zero && e1 == e2 && p1.isPure) { assert(p2.isPure); oneSig }
          else sig

        case Signature(Label.BVNot, Seq(e)) =>
          code2sig(e) match {
            case Signature(Label.BVNot, Seq(e2)) => code2sig(e2)
            case _ => sig
          }

        case Signature(Label.BVAnd, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); code2sig(e1) }
          else if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); zeroSig }
          else sig

        case Signature(Label.BVOr, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); code2sig(e1) }
          else if (e1 == zero) { assert(p1.isPure); code2sig(e2) }
          else if (e2 == zero) { assert(p2.isPure); code2sig(e1) }
          else sig

        case Signature(Label.BVXor, Seq(e1, e2)) =>
          val p1 = codePurity(e1)
          val p2 = codePurity(e2)
          if (e1 == e2 && p1.isPure) { assert(p2.isPure); zeroSig }
          else if (e1 == zero) { assert(p1.isPure); code2sig(e2) }
          else if (e2 == zero) { assert(p2.isPure); code2sig(e1) }
          else sig

        case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
          val p2 = codePurity(e2)
          if (e2 == zero) {assert(p2.isPure); code2sig(e1) }
          else sig

        case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
          // TODO: Il faudra supposer que scrut est let-bound?
          assert(2 * pats.size == guardRhs.size)
          val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
          val cases = pats.zip(guards).zip(rhss).map {
            case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
          }
          // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
          // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
          // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
          val rscrut = transform(scrut, repl, ())
          simplifyCases(rscrut, cases, repl + (scrut -> rscrut), Seq.empty) match {
            case (Seq(), _) =>
              ???
            case (Seq(matchCase), true) =>
              // Remarque: si allCovered = true, alors on a forcément un wildcard pattern (et aucune subst n'est nécessaire)
              assert(matchCase.pattern.isInstanceOf[LabelledPattern.Wildcard])
              code2sig(matchCase.rhs)
            case (newCases, _) =>
              mkMatchExpr(rscrut, newCases)
          }

        case _ => super.transformImpl(sig, tpe, repl, extra) // TODO: Ici, on call super.transformImpl pour faire appel à "l'original". Si on transform(..), cela va loop
      }
    }

    def simplifyCase(newScrut: Code, matchCase: LabMatchCase, repl: Map[Code, Code])(using env: OEnv): Option[(LabMatchCase, Seq[Code], Boolean)] = {
      // Remarque: comme il n'y pas de binder explicit, il n'y a rien a freshen.
      val (newMatchCase, caseConds) = transformCase(matchCase, repl, ())
      if (codePurity(newScrut).isPure && caseConds.forall(c => codePurity(c).isPure)) {
        val envWithConds = env.withConds(caseConds.toSet)
        if (implied(trueCode)(using envWithConds)) {
          // Remarque: comme on ne bind pas explicitement les patterns (mais qu'on crée des node select avec edges vers newScrut),
          // on n'a pas besoin "d'adapter" le rhs dû au remplacement du pattern par un wildcard.
          return Some(LabMatchCase(LabelledPattern.Wildcard(newScrut), trueCode, newMatchCase.rhs), Seq(trueCode), true)
        } else if (implied(falseCode)(using envWithConds)) {
          // This `matchCase` is unreachable
          return None
        }
      }

      Some(newMatchCase, caseConds, false)
    }

    def simplifyCases(newScrut: Code, cases: Seq[LabMatchCase], repl: Map[Code, Code], acc: Seq[LabMatchCase])(using env: OEnv): (Seq[LabMatchCase], Boolean) = {
      if (cases.isEmpty) (acc, false)
      else {
        // TODO: Envs ok? Apres tout, on pourrait accumuler les accumulated conds dans env non?
        simplifyCase(newScrut, cases.head, repl) match {
          case Some((newMatchCase, caseConds, allCovered)) =>
            if (allCovered && caseConds.forall(c => codePurity(c).isPure)) (acc :+ newMatchCase, true)
            else {
              val negCaseConds = negatedConjunction(caseConds)
              simplifyCases(newScrut, cases.tail, repl, acc :+ newMatchCase)(using env.withCond(negCaseConds))
            }
          case None =>
            simplifyCases(newScrut, cases.tail, repl, acc)
        }
      }
    }

  }
  */

  class SigPurity extends CodeTryFolder[Unit, Purity](depthLimit = None) {
    override type Extra = Unit

    override def tryFoldImpl(sig: Signature, acc: Purity, extra: Unit)(using env: OEnv): Either[Unit, Purity] = {
      val p = acc ++ sigPurity(sig) // Remarque: ++ est lazy sur sa droite, donc si acc est impure, on ne va pas calculer sigPurityIn
      if (p == Impure) Left(())
      else Right(p)
    }

    // TODO: Caching
    // TODO: Ce truc avec les Delayed et les blocked by???
    def codePurity(c: Code)(using env: OEnv): Purity = {
      // TODO: On pourrait utiliser un "revLetDef" dans env
      if (env.letDef.exists(_._2._1 == c)) Pure
      else sigPurity(code2sig(c))
    }

    def sigPurity(sig: Signature)(using env: OEnv): Purity = sig match {
      case Signature(Label.Var(_) | Label.Lit(_), Seq()) => Pure
      case Signature(Label.Assume, Seq(pred, body)) =>
        if (pred == trueCode) codePurity(body) // pas besoin de env.withCond car de toute façon c'est true
        else Impure

      case Signature(Label.Assert, Seq(pred, body)) =>
        val pBody = codePurity(body)(using env.withCond(pred))
        if (pred == trueCode) pBody
        else assmChkPurity ++ pBody // Pureté comme Stainless

      case Signature(Label.Require, Seq(pred, body)) =>
        val pBody = codePurity(body)(using env.withCond(pred))
        if (pred == trueCode) pBody
        else assmChkPurity ++ pBody // Ditto

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        code2sig(pred) match {
          case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => codePurity(body)
          case _ => Impure
        }

      case Signature(Label.ADTSelector(adt, ctor, _), Seq(e)) =>
        // Remarque: on ne souhaite pas faire dépendre la pureté d'une sig en fn. de env!!!
        if (opts.assumeChecked || isConstructor(e, adt, ctor.id)/*(using OEnv.empty)*/ == Some(true)) codePurity(e)
        else Impure

      case Signature(Label.ADT(id, tps), args) =>
        // TODO: Ok? Il y a un commentaire dans SWP...
        val ctor: TypedADTConstructor = getConstructor(id, tps)
        val consingPurity = {
          if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
          else Impure
        }
        consingPurity ++ fold(args.map(codePurity))

      case Signature(Label.Lambda(_), Seq(_)) => Pure

      case Signature(Label.FunctionInvocation(id, _), args) =>
        fold(args.map(codePurity)) ++ fnPurity(id)

      case Signature(Label.Application, callee +: args) =>
        // TODO: Pureté ok? Après tout, un inline de lambda peut donner lieu à impure...
        assmChkPurity ++ fold(args.map(codePurity))

      case Signature(Label.Choose(v), Seq(pred)) =>
        if (pred == trueCode && hasInstance(varTpe(v)) == Some(true)) Pure
        else Impure

      // TODO: Pureté ok pour NoTree/Error? Car dans SWP et isImpure, aucune mention de NoTree/Error...
      case Signature(Label.Division | Label.Remainder | Label.Modulo | Label.NoTree(_) | Label.Error(_, _), _) =>
        assmChkPurity // TODO: Ok?

      // TODO: Pureté de Decreases?
      // TODO: Array select, map select, etc.???

      case sig => super.tryFoldImpl(sig, Pure, ()).getOrElse(Impure)
    }
  }

  // TODO: Commentaire à propos de code potentiel dans les labels qui ne sont pas transform
  class CodeTransformer(val depthLimit: Option[Int] = None) {
    type Extra
    var currDepthLimit = depthLimit
    var depth = 0

    final def transform(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Extra)(using OEnv, InLambda): CodeRes = {
      // Si la signature a un code, alors on ne devrait pas le retrouver dans repl (autrement, on manquerait une transformation)
      assert(sig2code.get(sig).forall(c => !repl.contains(c)))
      if (currDepthLimit.exists(_ <= depth)) ???
      else {
        depth += 1
        val res = transformImpl(sig, tpe, repl, extra)
        depth -= 1
        res
      }
    }

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using OEnv, InLambda): CodeRes = {
      repl.get(c) match {
        case Some(cc) =>
          // Si cc est une var à un enclosing let, on le remplace par sa définition (pr autant que cela est permis)
          val res = code2sig(cc) match {
            case Signature(Label.Var(v), Seq()) =>
              substByLet(v).getOrElse(cc)
            case _ => cc
          }
          // TODO: termHasLambdaDef ok??? et si v est une ref. à une lambda???
          CodeRes.of(res, termHasLambdaDef = false)
        case None =>
          transform(code2sig(c), codeTpe(c), repl, extra)
      }
    }

    def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Extra)(using env: OEnv, inLambda: InLambda): CodeRes = sig match {
      case Signature(Label.Var(v), Seq()) =>
        val res = substByLet(v).getOrElse(codeOfVarId(v))
        // TODO: termHasLambdaDef ok??? et si v est une ref. à une lambda???
        CodeRes.of(res, termHasLambdaDef = false)
      case Signature(Label.Let(v), Seq(e, b)) =>
        ???
//        val re = transform(e, repl, extra)
//        val rb = transform(b, repl + (e -> re), extra)(using env.withLetBound(v, re, canSubst = canSubstLet(re)))
//        mkLet(v, re, rb)
    }

    // Note: peut être "stacké"
    final def withIncreaseDepth[T](added: Int)(body: => T): T = {
      val currSaved = currDepthLimit
      currDepthLimit = currDepthLimit.map(_ + added)
      val res = body
      currDepthLimit = currSaved
      res
    }

    def canSubstLet(c: Code): Boolean = !isLambda(c)

    /*
    // TODO: TODO: Faire la remarque les les .withCond injecté sont issues *après* la transformation, et pas les "originaux"!
    def transformImpl(sig: Signature, tpe: Type, repl: Map[Code, Code], extra: Extra)(using env: OEnv): Signature = sig match {
      // TODO: Quid subst des let????
      // TODO: Quid subst des let????
      // TODO: Quid subst des let????
      // TODO: Quid subst des let???? --> mettre un case ici pr les var
      //    -> ça sert à rien non? De toute façon, on suppose qu'on utilise déjà les defs non???

      case Signature(Label.Var(v), Seq()) =>
        substByLet(v).map(code2sig).getOrElse(sig)

      case Signature(Label.Let(v), Seq(e, b)) =>
        val re = transform(e, repl, extra)
        val rb = transform(b, repl + (e -> re), extra)(using env.withLetBound(v, re, canSubst = canSubstLet(re)))
        mkLet(v, re, rb)

      case Signature(Label.Assert, Seq(pred, body)) =>
        val rpred = transform(pred, repl, extra)
        val rbody = transform(body, repl, extra)(using env.withCond(rpred))
        mkAssert(rpred, rbody)

      case Signature(Label.Assume, Seq(pred, body)) =>
        val rpred = transform(pred, repl, extra)
        val rbody = transform(body, repl, extra)(using env.withCond(rpred))
        mkAssume(rpred, rbody)

      case Signature(Label.Require, Seq(pred, body)) =>
        val rpred = transform(pred, repl, extra)
        val rbody = transform(body, repl, extra)(using env.withCond(rpred))
        mkRequire(rpred, rbody)

      case Signature(Label.Or, args) =>
        val rargs = args.foldLeft((Seq.empty[Code], env)) {
          case ((acc, env), arg) =>
            given OEnv = env
            val rarg = transform(arg, repl, extra)
            (acc :+ rarg, env.withCond(negCodeOf(rarg)))
        }._1
        mkOr(rargs)

      case Signature(Label.IfExpr, Seq(c, thn, els)) =>
        val rc = transform(c, repl, extra)
        val rthn = transform(thn, repl, extra)(using env.withCond(rc))
        val rels = transform(els, repl, extra)(using env.withCond(negCodeOf(rc)))
        mkIfExpr(rc, rthn, rels)

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val cases = pats.zip(guards).zip(rhss).map {
          case ((pat, guard), rhs) => LabMatchCase(pat, guard, rhs)
        }
        // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
        // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
        // TODO: Il faudra supposer que scrut est let-bound? --> mettre assertion que transformé est let-bound!!!
        val rscrut = transform(scrut, repl, extra)
        val newCases = transformCases(cases, repl + (scrut -> rscrut), extra, Seq.empty)
        mkMatchExpr(rscrut, newCases)

      // TODO: Suppose que lab pas besoin d'avoir des sous parties transformées. P.ex. pour MatchExpr, cela ne jouera pas (en raison des recs?)
      case Signature(lab, children) =>
        val rchildren = children.map(transform(_, repl, extra))
        Signature(lab, rchildren)
    }

    final def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: OEnv): Code = {
      val tpe = codeTpe(c)
      val newSig = transformImpl(code2sig(c), tpe, repl, extra)
      codeOfSig(newSig, tpe)
    }

    def transformCases(cases: Seq[LabMatchCase], repl: Map[Code, Code], extra: Extra, acc: Seq[LabMatchCase])(using env: OEnv): Seq[LabMatchCase] = {
      if (cases.isEmpty) acc
      else {
        val (newMatchCase, caseConds) = transformCase(cases.head, repl, extra)
        val negCaseConds = negatedConjunction(caseConds)
        transformCases(cases.tail, repl, extra, acc :+ newMatchCase)(using env.withCond(negCaseConds))
      }
    }

    def transformCase(matchCase: LabMatchCase, repl: Map[Code, Code], extra: Extra)(using env: OEnv): (LabMatchCase, Seq[Code]) = {
      val newPat = replaceIn(matchCase.pattern, repl)
      val patConds = collectPatternConds(newPat, recursive = true)
      val rguard = transform(matchCase.guard, repl, extra)(using env.withConds(patConds.toSet))
      val caseConds = patConds :+ rguard
      val rrhs = transform(matchCase.rhs, repl, extra)(using env.withConds(caseConds.toSet))
      (LabMatchCase(newPat, rguard, rrhs), caseConds)
    }
    */
  }

  class CodeTryFolder[E, T](val depthLimit: Option[Int] = None) {
    type Extra
    var currDepthLimit = depthLimit
    var depth = 0

    final def tryFold(sig: Signature, acc: T, extra: Extra)(using OEnv): Either[E, T] = {
      if (currDepthLimit.exists(_ <= depth)) limitDepthReached(sig, acc, extra)
      else {
        depth += 1
        val res = tryFoldImpl(sig, acc, extra)
        depth -= 1
        res
      }
    }

    final def tryFold(c: Code, acc: T, extra: Extra)(using OEnv): Either[E, T] = tryFold(code2sig(c), acc, extra)

    def limitDepthReached(sig: Signature, acc: T, extra: Extra)(using OEnv): Either[E, T] = Right(acc)

    def canSubstLet(c: Code): Boolean = !isLambda(c)

    final def tryFoldImpl(c: Code, acc: T, extra: Extra)(using env: OEnv): Either[E, T] =
      tryFoldImpl(code2sig(c), acc, extra)

    def tryFoldImpl(sig: Signature, acc: T, extra: Extra)(using env: OEnv): Either[E, T] = sig match {
      // TODO: Quid subst des let???? --> mettre un case ici pr les var
      //    -> ça sert à rien non? De toute façon, on suppose qu'on utilise déjà les defs non???

      case Signature(Label.Var(v), Seq()) =>
        substByLet(v).map(tryFold(_, acc, extra)).getOrElse(Right(acc))

      case Signature(Label.Let(v), Seq(e, b)) =>
        for {
          re <- tryFold(e, acc, extra)
          rb <- tryFold(b, re, extra)(using env.withLetBound(v, e, canSubst = canSubstLet(e)))
        } yield rb

      case Signature(Label.Assert | Label.Assume | Label.Require, Seq(pred, body)) =>
        for {
          rpred <- tryFold(pred, acc, extra)
          rbody <- tryFold(body, rpred, extra)(using env.withCond(pred))
        } yield rbody

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        for {
          rcond <- tryFold(cond, acc, extra)
          rthn <- tryFold(thn, rcond, extra)(using env.withCond(cond))
          rels <- tryFold(els, rthn, extra)(using env.withCond(negCodeOf(cond)))
        } yield rels

      case Signature(Label.Or, args) =>
        tryFoldSeq(args, acc, extra) { case (disj, env) => env.withCond(negCodeOf(disj)(using env)) }

      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        val (guards, rhss) = guardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        val rscrut = tryFold(scrut, acc, extra)
        pats.zip(guards).zip(rhss).foldLeft(rscrut.map((_, env))) {
          case (Right((acc, env)), ((pat, guard), rhs)) =>
            val patConds = collectPatternConds(pat, recursive = true)
            for {
              rpat <- tryFoldSeq(patConds, acc, extra)
              rguard <- tryFold(guard, rpat, extra)(using env.withConds(patConds.toSet))
              caseConds = patConds :+ guard
              rrhs <- tryFold(rhs, rguard, extra)(using env.withConds(caseConds.toSet))
              negCaseConds = negatedConjunction(caseConds)
            } yield (rrhs, env.withCond(negCaseConds))
          case (Left(e), _) => Left(e)
        }.map(_._1)

      // TODO: Suppose que lab pas besoin d'avoir des sous parties transformées. P.ex. pour MatchExpr, cela ne jouera pas (en raison des recs?)
      case Signature(_, children) => tryFoldSeq(children, acc, extra)
    }

    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(using OEnv): Either[E, T] =
      tryFoldSeq(cs, acc, extra)((_, env) => env)

    // TODO: Dire que le nextEnv est appliqué pour le suivant (et pas pr le "current")
    final def tryFoldSeq(cs: Seq[Code], acc: T, extra: Extra)(nextEnv: (Code, OEnv) => OEnv)(using env: OEnv): Either[E, T] = {
      cs.foldLeft(Right((acc, env)): Either[E, (T, OEnv)]) {
        case (Right((acc, env)), c) =>
          tryFold(c, acc, extra).map((_, nextEnv(c, env)))
        case (Left(e), _) => Left(e) // should do an early return...
      }.map(_._1)
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Map all codes to their corresponding signatures (for debugging purposes)

  case class ExplicitSig(label: Label, children: Seq[ExplicitSig]) {
    override def toString: String = {
      if (children.isEmpty) label.toString
      else s"($label, ${children.mkString(", ")})"
    }
  }

  def asExplicitSig(c: Code): ExplicitSig = {
    val sig = code2sig(c)
    ExplicitSig(sig.label, sig.children.map(asExplicitSig))
  }
}

object OCBSL {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): OCBSL{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends OCBSL
    new Impl(t, s, opts)
  }
}