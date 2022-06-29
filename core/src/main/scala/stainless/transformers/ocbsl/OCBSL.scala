package stainless
package transformers
package ocbsl

import inox.solvers

// TODO: Certains Or ne semble pas correctement être flattened
// TODO: Inline les lambda (surtout pour les equations)
// TODO: Not(Or(..)) => And dans uncodeOf
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
// TODO: Non!!!! L'ordre des disjunction a de l'importance
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
                  bound: Map[Variable, BinderIx],
                  scopeLevel: Int,
                  // variable -> code de la *definition* pas de le code de l'indexed var
                  // et si on peut utiliser ce code là au lieu de l'indexed var.
                  // "true" en général, sauf pour les lambdas dans la var apparait plsrs fois.
                  // Le "uncodeOf" se débrouillera pour faire la substitution inverse, du code de la def à la var
                  letDef: Map[Variable, (Code, Boolean)]) {
    def withCond(c: Code): OEnv = copy(conditions = conditions + c)
    def withConds(cs: Set[Code]): OEnv = copy(conditions = conditions ++ cs)

    def withLetBound(vd: ValDef, c: Code, canSubst: Boolean): OEnv = withLetBounds(Seq((vd, c)), canSubst)

    def withLetBounds(vds: Seq[(ValDef, Code)], canSubst: Boolean): OEnv = {
      // Note: params may be empty, which is fine (the nesting level will not increase)

      assert(letDef.keySet.intersect(vds.map(_._1.toVariable).toSet).isEmpty)

      OEnv(conditions,
        bound ++ vds.zipWithIndex.map { case ((vd, _), i) => vd.toVariable -> BinderIx.fromScopeLevel(scopeLevel + i) }.toMap,
        scopeLevel + vds.size,
        letDef ++ vds.map((vd, c) => vd.toVariable -> (c, canSubst)))
    }

    def withOpenBound(param: ValDef): OEnv = withOpenBounds(Seq(param))

    def withOpenBounds(params: Seq[ValDef]): OEnv = {
      // Note: params may be empty, which is fine (the nesting level will not increase)
      OEnv(conditions,
        bound ++ params.zipWithIndex.map((vd, i) => vd.toVariable -> BinderIx.fromScopeLevel(scopeLevel + i)).toMap,
        scopeLevel + params.size, letDef)
    }
  }
  object OEnv {
    def empty: OEnv = OEnv(Set.empty, Map.empty, 0, Map.empty)
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???
  // TODO: Et les assms???

  // TODO: On pourrait simplifier les trucs du genre !isInstanceOf[A] && isInstanceOf[B] en isInstanceOf[B] pour les patmat?

  // TODO (liste de rappel):
  //    - Pour le "uncodeOf", pour éviter des duplication, on pourra let-bind les codes pour lesquelles
  //    les expr. sont non triviales
  //    - Pourrait-on envisager de supprimer les indexed var pour les lets (slmt pour les lets) et simplement utiliser les codes
  //    des definitions? On maintiendra un Let(def, body) et le "uncodeOf" pourra l'utiliser pour savoir
  //    où remettre le let (et là, on pourra même le supprimer si def est pas utilisé et qu'il est pur)
  //    Cela nous permettra d'éviter de devoir faire des substitutions explicites
  //      - Attention au gag avec les lambdas!! On risquera de tout inliner dans le truc de simplification...
  //        Sauf si: On arrive a flairer le truc et qu'on arrive a voir combien il y a de references a cette lambda
  //        si cest let-bound etc.


  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: Comment mélanger caching et simplification (p.ex. simplifiedDisjunction)?

  private val sig2code = mutable.Map.empty[Signature, Code]
  private val code2sig = mutable.Map.empty[Code, Signature]
  private val sizeCache = mutable.Map.empty[Expr, Int]
  private val codeTpe = mutable.Map.empty[Code, Type]

  private val purityCache = mutable.Map.empty[Identifier, Boolean]
  private val codePurityCache = mutable.Map.empty[Code, Boolean]
  private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn qui est bloqué par les fn dans V
  private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code qui est bloqué par les fn dans V
  private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn qui bloque les fn et les codes dans V
  private val visiting = mutable.Set.empty[Identifier]

  private val falseSig = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
  private val trueSig = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
  private val falseCode = updateCodesSig(falseSig, Pure, BooleanType())
  private val trueCode = updateCodesSig(trueSig, Pure, BooleanType())

  def codeOf(e: Expr)(using OEnv): Code = {
    if (e.getType == BooleanType()) simplifiedDisjunction(pDisj(e).toSet)
    else {
      val (sig, p) = computeSignature(e)
      updateCodesSig(sig, p, e.getType)
    }
  }

  def negCodeOf(c: Code)(using OEnv): Code = updateCodesSig(pNegNormal(c), codePurity(c), BooleanType())

  // TODO: Pk ce truc est fait dans codeOf mais pas dans pDisj?
  // TODO: Et les assms???
  def simplifiedDisjunction(disj: Set[Code]): Code = {
    assert(disj.forall(c => codeTpe(c) == BooleanType()))
    // TODO: Caching?
    val purity = fold(disj.map(codePurity).toSeq)
    val disj1 = disj.filter(_ != falseCode)
    if (disj1.isEmpty) falseCode
    else if (disj1.size == 1) disj1.head
    else if (purity.isPure && (disj1.contains(trueCode) || checkForContradiction(disj1))) trueCode
    else {
      val sig = Signature(Label.Or, disj1.toSeq.sorted)
      updateCodesSig(sig, purity, BooleanType())
    }
  }

  def computeSignature(e: Expr)(using env: OEnv): (Signature, Purity) = {
    val tpe = e.getType
    val (sig, purity) = e match {
      case v: Variable => sigOfVariable(v)
      case l: Literal[_] => (mkLit(l), Pure)

      case Assume(pred, body) =>
        val cPred = codeOf(pred)
        val cBody = codeOf(body)(using env.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
        simplifySigTopLvl(mkAssume(cPred, cBody), tpe)

      case Assert(pred, _, body) =>
        val cPred = codeOf(pred)
        val cBody = codeOf(body)(using env.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
        simplifySigTopLvl(mkAssert(cPred, cBody), tpe)

      case Require(pred, body) =>
        val cPred = codeOf(pred)
        val cBody = codeOf(body)(using env.withCond(cPred)) // TODO: Si on ajoute false, est-ce que ça joue qd meme?
        simplifySigTopLvl(mkRequire(cPred, cBody), tpe)

      case Ensuring(body, pred) =>
        simplifySigTopLvl(mkEnsuring(codeOf(body), codeOf(pred)), tpe)

      case Decreases(measure, body) =>
        simplifySigTopLvl(mkDecreases(codeOf(measure), codeOf(body)), tpe)

      case Tuple(args) =>
        simplifySigTopLvl(mkTuple(args.map(codeOf)), tpe)

      case ADT(id, tps, args) =>
        simplifySigTopLvl(mkADT(id, tps, args.map(codeOf)), tpe)

      case s @ ADTSelector(e, selector) =>
        val adt @ ADTType(_, _) = e.getType
        simplifySigTopLvl(mkADTSelector(codeOf(e), adt, s.constructor, selector), tpe)

      case FunctionInvocation(id, tps, args) =>
        val cs = args.map(codeOf)
        // TODO: Pk ne pousse-t-on pas cela dans simplifyTopLvlSig??
        val purity = fold(cs.map(codePurity)) ++ fnPurity(id)
        (mkFunInvoc(id, tps, cs), purity) // TODO

      case Application(callee, args) =>
        simplifySigTopLvl(mkApp(codeOf(callee), args.map(codeOf)), tpe)

      // TODO: Pour les cas ou on a besoin d'une réponse "tout de suite" pour procéder à des simplification, comment s'y prendre???
      case IfExpr(cond, thenn, elze) =>
        val cCond = codeOf(cond)
        // TODO: Si on ajoute false, est-ce que ça joue qd meme?
        val cThen = codeOf(thenn)(using env.withCond(cCond))
        val cElse = codeOf(elze)(using env.withCond(negCodeOf(cCond)))
        simplifySigTopLvl(mkIfExpr(cCond, cThen, cElse), tpe)

      case IsConstructor(e, id) =>
        val adt @ ADTType(_, _) = e.getType
        simplifySigTopLvl(mkIsCtor(codeOf(e), adt, id), tpe)

      // TODO: Let of ADT???
      // TODO: Let of ADT???
      // TODO: Let of ADT???
      case Let(vd, e, body) =>
        val cE = codeOf(e)
        // TODO: Ok par rapport à la pureté et ces subst?
        val canSubst = code2sig(cE) match {
          case Signature(Label.Lambda(_), _) =>
            val v = vd.toVariable
            // TODO: Par rapport à orig body, et pas simplified body --'
            // TODO: !!!! ??? immediateCall + inLambda ??? !!!!
            //    pour le "immediateCall": ? p-e par rapport au path condition supplémentaire résultant de stmts intermediaire avant le call?
            //    pour le "inLambda": pour eviter explosion en cas d'inling lambda (~> à gérer dans "uncodeOf"?)
            exprOps.count { case `v` => 1 case _ => 0 } (body) <= 1
          case _ => true
        }
        val cB = codeOf(body)(using env.withLetBound(vd, cE, canSubst))
        simplifySigTopLvl(mkLet(cE, cB), tpe)

      case Lambda(params, body) =>
        val c = codeOf(body)(using env.withOpenBounds(params))
        simplifySigTopLvl(mkLambda(params.map(_.getType), c), tpe)

      case Choose(res, pred) =>
        val c = codeOf(pred)(using env.withOpenBound(res))
        simplifySigTopLvl(mkWickedChoose(res.getType, c), tpe)

      case Forall(params, body) =>
        val c = codeOf(body)(using env.withOpenBounds(params))
        simplifySigTopLvl(mkForall(params.map(_.getType), c), tpe)

      // TODO: Annotated peut empecher certaines simplif. non? Voir la PR de Georg.
      // TODO: On pourrait p-e ignorer Annotated? De toute façon, si c'est pour avoir des DropVCs, cela ne change rien dans notre cas de figure?
      //  -> sauf p-e si on fait un "uncodeOf" et qu'on a besoin de restaurer certaines annotation, mais là on pourrait p-e envisager
      //  une map ad-hoc qui contient ces infos...?
      case Annotated(e, flags) =>
        // TODO: Gros gag: pourrait-on envisager d'assigner le même code pour la sig. de Annotated que pour la sig. de e ????
        //    Il faudra faire cette update un peu hacky à la fin. On aura besoin de manip les 2 maps par nous meme
        //    sans passer par updateCodeSig. On devra également avoir une map auxiliaire qui se souvient des exprs annotées pour ce uncodeOf...
        simplifySigTopLvl(mkAnnot(codeOf(e), flags), tpe)

      // TODO: Ne pourrait-on pas envisager certains simplif. ici? Pk "attendre" codeOf?
      case and @ And(_) =>
        val ands = unAnd(and)
        val c = codeOf(Not(Or(ands.map(Not.apply))))
        (code2sig(c), codePurity(c))
      case or @ Or(_) =>
        // TODO: checkForContradiction?
        // TODO: Pas d'incohérence avec purity? (p.ex. un code qui est pure, mais pas l'autre)?
        // TODO: Devrait-on ajouter withCond avec les negation des precedents? Ou est-ce que cela risque d'interferer avec OCBSL?
        val cs = unOr(or).map(codeOf).sorted.distinct
        // TODO: Move simplifyTopLvlSig
        (mkOr(cs), fold(cs.map(codePurity)))
      case Not(e) => pNeg(e) // TODO: ? pk pas simplifyTopLvlSig?
      case Implies(e1, e2) =>
        val c = codeOf(Or(Not(e1), e2))
        (code2sig(c), codePurity(c))
      case Equals(e1, e2) =>
        simplifySigTopLvl(mkEquals(codeOf(e1), codeOf(e2)), tpe)
      case LessThan(e1, e2) =>
        simplifySigTopLvl(mkLessThan(codeOf(e1), codeOf(e2)), tpe)
      case GreaterThan(e1, e2) =>
        simplifySigTopLvl(mkGreaterThan(codeOf(e1), codeOf(e2)), tpe)
      case LessEquals(e1, e2) =>
        simplifySigTopLvl(mkLessEquals(codeOf(e1), codeOf(e2)), tpe)
      case GreaterEquals(e1, e2) =>
        simplifySigTopLvl(mkGreaterEquals(codeOf(e1), codeOf(e2)), tpe)
      case UMinus(e) =>
        simplifySigTopLvl(mkUMinus(codeOf(e)), tpe)

      case Plus(e1, e2) =>
        simplifySigTopLvl(mkPlus(codeOf(e1), codeOf(e2)), tpe)
      case Minus(e1, e2) =>
        simplifySigTopLvl(mkMinus(codeOf(e1), codeOf(e2)), tpe)
      case Times(e1, e2) =>
        simplifySigTopLvl(mkTimes(codeOf(e1), codeOf(e2)), tpe)
      case Division(e1, e2) =>
        simplifySigTopLvl(mkDivision(codeOf(e1), codeOf(e2)), tpe)
      case Remainder(e1, e2) =>
        simplifySigTopLvl(mkRemainder(codeOf(e1), codeOf(e2)), tpe)
      case Modulo(e1, e2) =>
        simplifySigTopLvl(mkModulo(codeOf(e1), codeOf(e2)), tpe)

      case BVNot(e) =>
        simplifySigTopLvl(mkBVNot(codeOf(e)), tpe)
      case BVAnd(e1, e2) =>
        simplifySigTopLvl(mkBVAnd(codeOf(e1), codeOf(e2)), tpe)
      case BVOr(e1, e2) =>
        simplifySigTopLvl(mkBVOr(codeOf(e1), codeOf(e2)), tpe)
      case BVXor(e1, e2) =>
        simplifySigTopLvl(mkBVXor(codeOf(e1), codeOf(e2)), tpe)
      case BVShiftLeft(e1, e2) =>
        simplifySigTopLvl(mkBVShiftLeft(codeOf(e1), codeOf(e2)), tpe)
      case BVAShiftRight(e1, e2) =>
        simplifySigTopLvl(mkBVAShiftRight(codeOf(e1), codeOf(e2)), tpe)
      case BVLShiftRight(e1, e2) =>
        simplifySigTopLvl(mkBVLShiftRight(codeOf(e1), codeOf(e2)), tpe)

      case BVNarrowingCast(e, newType) =>
        simplifySigTopLvl(mkBVNarrowingCast(codeOf(e), newType), tpe)
      case BVWideningCast(e, newType) =>
        simplifySigTopLvl(mkBVWideningCast(codeOf(e), newType), tpe)
      case BVUnsignedToSigned(e) =>
        simplifySigTopLvl(mkBVUnsignedToSigned(codeOf(e)), tpe)
      case BVSignedToUnsigned(e) =>
        simplifySigTopLvl(mkBVUnsignedToSigned(codeOf(e)), tpe)

      case TupleSelect(e, index) =>
        simplifySigTopLvl(mkTupleSelect(codeOf(e), index), tpe)

      case FiniteSet(elems, base) =>
        simplifySigTopLvl(mkFiniteSet(elems.map(codeOf), base), tpe)
      case SetAdd(set, elem) =>
        simplifySigTopLvl(mkSetAdd(codeOf(set), codeOf(elem)), tpe)
      case ElementOfSet(elem, set) =>
        simplifySigTopLvl(mkElementOfSet(codeOf(elem), codeOf(set)), tpe)
      case SubsetOf(lhs, rhs) =>
        simplifySigTopLvl(mkSubsetOf(codeOf(lhs), codeOf(rhs)), tpe)
      case SetIntersection(lhs, rhs) =>
        simplifySigTopLvl(mkSetIntersection(codeOf(lhs), codeOf(rhs)), tpe)
      case SetUnion(lhs, rhs) =>
        simplifySigTopLvl(mkSetUnion(codeOf(lhs), codeOf(rhs)), tpe)
      case SetDifference(lhs, rhs) =>
        simplifySigTopLvl(mkSetDifference(codeOf(lhs), codeOf(rhs)), tpe)

      case FiniteArray(elems, base) =>
        simplifySigTopLvl(mkFiniteArray(elems.map(codeOf), base), tpe)
      case LargeArray(elems, default, size, base) =>
        simplifySigTopLvl(mkLargeArray(elems.map((i, e) => i -> codeOf(e)), codeOf(default), codeOf(size), base), tpe)
      case ArraySelect(array, index) =>
        simplifySigTopLvl(mkArraySelect(codeOf(array), codeOf(index)), tpe)
      case ArrayUpdated(array, index, value) =>
        simplifySigTopLvl(mkArrayUpdated(codeOf(array), codeOf(index), codeOf(value)), tpe)
      case ArrayLength(array) =>
        simplifySigTopLvl(mkArrayLength(codeOf(array)), tpe)

      case Error(ofTpe, descr) => simplifySigTopLvl(mkError(ofTpe, descr), tpe)
      case NoTree(ofTpe) => simplifySigTopLvl(mkNoTree(ofTpe), tpe)

      // TODO: Passer en revue la pureté: p.ex. si on est pas exhaustif, devrait-on retourner "assumeChecked"?
      // Yes, go down right there, you are painful to deal with!!!
      case MatchExpr(scrut, cases) =>
        def processPattern(subScrut: Code, scrutTpe: Type, pat: Pattern): (LabelledPattern, Seq[(ValDef, Code)], Set[Code]) = {
          // On doit être vigilent avec les env implicites qu'on utilise!!!
          given dontDefaultUseOuterEnv: OEnv = sys.error("Carefully consider the appropriate env to use")
          val pSubScrut = codePurity(subScrut)
          val vdBinder: ValDef = pat.binder.getOrElse(ValDef.fresh("dummyBinder", scrutTpe))
          val bdgs1 = Seq((vdBinder, subScrut))
          pat match {
            case WildcardPattern(_) => (LabelledPattern.Wildcard(subScrut), bdgs1, Set.empty)
            case ADTPattern(_, id, tps, subps) =>
              val adt = ADTType(id, tps)
              val tcons = getConstructor(id, tps)
              assert(tcons.fields.size == subps.size)

              val conds1 = {
                // Using `simplifySigTopLvl` here as it can reduce to `true` if this ADT is the only ctor
                val (isCtorSig, _) = simplifySigTopLvl(mkIsCtor(subScrut, adt, id), BooleanType())(using env) // TODO: Default env ok?
                updateCodesSig(isCtorSig, pSubScrut, BooleanType())
              }
              val (labSubPats, bdgs2, conds2) = tcons.fields.zip(subps).foldLeft((Seq.empty[LabelledPattern], bdgs1, Set(conds1))) {
                // TODO: Annoté en dropvc?
                case ((labSubPatAcc, bdgsAcc, condsAcc), (fld, subpat)) =>
                  // TODO: Il nous faut un adt selector
                  // TODO: Ok????
                  // TODO: Purity de toussa??? devrait on inclure purity scrut???
                  val newScrut = updateCodesSig(mkADTSelector(subScrut, adt, tcons, fld.id), pSubScrut, fld.getType)
                  val (labSubPat, newBdgs, newConds) = processPattern(newScrut, fld.getType, subpat)
                  (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
              }
              (LabelledPattern.ADT(subScrut, id, tps, labSubPats), bdgs2, conds2)
            case TuplePattern(_, subps) =>
              val TupleType(bases) = scrutTpe
              assert(bases.size == subps.size)
              val (labSubPats, bdgs2, conds) = subps.zipWithIndex.foldLeft((Seq.empty[LabelledPattern], bdgs1, Set.empty[Code])) {
                case ((labSubPatAcc, bdgsAcc, condsAcc), (subpat, i)) =>
                  // TODO: Purity de toussa??? devrait on inclure purity scrut???
                  val newScrutTpe = bases(i)
                  val newScrut = updateCodesSig(mkTupleSelect(subScrut, i + 1), pSubScrut, newScrutTpe)
                  val (labSubPat, newBdgs, newConds) = processPattern(newScrut, newScrutTpe, subpat)
                  (labSubPatAcc :+ labSubPat, bdgsAcc ++ newBdgs, condsAcc ++ newConds)
              }
              (LabelledPattern.TuplePattern(subScrut, labSubPats), bdgs2, conds)
            case LiteralPattern(_, lit) => (LabelledPattern.Lit(subScrut ,lit), bdgs1, Set.empty)
            case UnapplyPattern(_, recs, id, tps, subps) =>
              // TODO: !!!! Si on utilise codeOf, ne pas oublier d'utiliser le subst approprié !!!
              sys.error(s"Does not know how to handle $pat")
          }
        }

        val cScrut = codeOf(scrut)
        val pScrut = codePurity(cScrut)

        // accumulatedConds: la negation des conds des cases antérieures
        def processCase(mc: MatchCase, accumulatedConds: Set[Code]): Option[(LabMatchCase, Set[Code], Boolean)] = {
          given dontDefaultUseOuterEnv: OEnv = sys.error("Carefully consider the appropriate env to use")
          // patConds: SANS le guard!!!
          val (labPat, bdgs, patConds) = processPattern(cScrut, scrut.getType, mc.pattern)
          // TODO: canSubst?
          val env1 = env.withLetBounds(bdgs, canSubst = true).withConds(accumulatedConds ++ patConds)
          val cGuard = mc.optGuard.map(codeOf(_)(using env1)).getOrElse(trueCode)
          val env2 = env1.withCond(cGuard)

          val cRhs = codeOf(mc.rhs)(using env2)
          if (pScrut.isPure) {
            // TODO: Ok par rapport à la pureté?

            if (implied(trueCode)(using env2)) {
              // TODO: A-t-on besoin de faire qqchose pour ces bindings?
              return Some(LabMatchCase(LabelledPattern.Wildcard(cScrut), trueCode, cRhs), Set(trueCode), true)
            } else if (implied(falseCode)(using env2)) {
              // Unreachable
              return None
            }
          }

          Some(LabMatchCase(labPat, cGuard, cRhs), patConds + cGuard, false)
        }

        def processCases(cases: Seq[MatchCase], accumulatedConds: Set[Code], acc: Seq[LabMatchCase]): (Seq[LabMatchCase], Boolean) = {
          given dontDefaultUseOuterEnv: OEnv = sys.error("Carefully consider the appropriate env to use")
          if (cases.isEmpty) (acc, false)
          else {
            processCase(cases.head, accumulatedConds) match {
              case Some((labMatchCase, caseConds, allCovered)) =>
                if (allCovered) (acc :+ labMatchCase, true)
                else {
                  val negCaseConds = negatedConjunction(caseConds)(using env)
                  processCases(cases.tail, accumulatedConds + negCaseConds, acc :+ labMatchCase)
                }
              case None =>
                processCases(cases.tail, accumulatedConds, acc)
            }
          }
        }

        // TODO: Quid pureté (surtout si pas exhaustif)???? Et celle des guard+rhs????
        processCases(cases, Set.empty, Seq.empty) match {
          // TODO: Et simplifySigTopLvl ???
          case (Seq(), _) =>
            ???
          case (Seq(matchCase), true) =>
            // Remarque: si allCovered = true, alors on a forcément un wildcard pattern (et aucune subst n'est nécessaire)
            assert(matchCase.pattern.isInstanceOf[LabelledPattern.Wildcard])
            // TODO: Et simplifySigTopLvl ???
            // TODO: Autre chose pour les bdgs?
            (code2sig(matchCase.rhs), pScrut ++ codePurity(matchCase.guard) ++ codePurity(matchCase.rhs))
          case (matchCases, _) =>
            // TODO: Et simplifySigTopLvl ???
            val purity = matchCases.foldLeft(pScrut) {
              case (p, LabMatchCase(_, guard, rhs)) => p ++ codePurity(guard) ++ codePurity(rhs)
            }
            (mkMatchExpr(cScrut, matchCases), purity)
        }

      case e =>
        println("computeSignature: Do not know how to handle "+e)
        ???
    }

    val code = updateCodesSig(sig, purity, tpe)
    val simpSig = {
      if (purity.isPure && tpe == BooleanType() && implied(code)) trueSig
      else sig
    }
    (simpSig, purity)
  }

  def checkForContradiction(disj: Set[Code]): Boolean = {
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
    assert(e.getType == BooleanType(), s"Got ${e.getType}")
    computeSignature(e) match {
      case (Signature(Label.Or, children), _) => children // TODO: Flatten more?
      case (Signature(Label.Not, Seq(c)), p) => Seq(updateCodesSig(pNegNormal(c), p, BooleanType())) // TODO: Ok?
      case (sig, p) => Seq(updateCodesSig(sig, p, BooleanType()))
    }
  }

  // TODO: Voir si on peut pas faire qqchose pr eviter code dup avec pNegNormal
  // Signature de Not(child)
  def pNeg(child: Expr)(using OEnv): (Signature, Purity) = {

    // TODO: Où devrait-on mettre le caching? C'est appelé par computeSignature donc ça devrait faire l'affaire non?

    child match {
      case Not(e) => computeSignature(e) // TODO: Orig fait pDisj, mais pDisj et un computeSignature pour nous (du moins, pour le moment)
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
          if (purity.isPure && (s.contains(trueCode) || checkForContradiction(s.toSet))) (falseSig, Pure)
          else if (s.size == 1) (pNegNormal(s.head), purity)
          else {
            val orCode = updateCodesSig(Signature(Label.Or, s), purity, BooleanType())
            (Signature(Label.Not, Seq(orCode)), purity)
          }
        }
      case _ =>
        // TODO: Ok?
        computeSignature(child) match {
          case (Signature(Label.Lit(BooleanLiteral(b)), Seq()), Pure) =>
            (Signature(Label.Lit(BooleanLiteral(!b)), Seq.empty), Pure)
          case (sig, purity) =>
            // TODO: Ok?
            (Signature(Label.Not, Seq(sig2code(sig))), purity)
        }
    }
  }

  // TODO: ok?
  // TODO: caching?
  // TODO: En gros la signature de Not(c)
  def pNegNormal(c: Code): Signature = {
    assert(code2sig.contains(c))
    code2sig(c) match {
      case Signature(Label.Not, Seq(cc)) => code2sig(cc)
      case Signature(_, _) => Signature(Label.Not, Seq(c)) // TODO: Ok?
    }
  }

  def simplifySigTopLvl(sig: Signature, tpe: Type)(using OEnv): (Signature, Purity) = {
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)
    lazy val zeroSig = code2sig(zero)
    lazy val oneSig = code2sig(one)

    sig match {
      case Signature(Label.Var(_) | Label.IndexedVar(_, _) | Label.Lit(_), Seq()) => (sig, Pure)
      case Signature(Label.Assume, Seq(pred, body)) =>
        if (pred == trueCode) (code2sig(body), codePurity(body))
        else if (pred == falseCode) (Signature(Label.Assume, Seq(falseCode, body)), Impure)
        else (sig, Impure)

      case Signature(Label.Assert, Seq(pred, body)) =>
        val pBody = codePurity(body)
        if (pred == trueCode) (code2sig(body), pBody)
        else if (pred == falseCode) (Signature(Label.Assert, Seq(falseCode, body)), assmChkPurity ++ pBody) // Purity comme Stainless
        else (sig, assmChkPurity ++ pBody) // Ditto

      case Signature(Label.Require, Seq(pred, body)) =>
        val pBody = codePurity(body)
        if (pred == trueCode) (code2sig(body), pBody)
        else (sig, assmChkPurity ++ pBody)

      case Signature(Label.Ensuring, Seq(body, pred)) =>
        code2sig(pred) match {
          case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => (code2sig(body), codePurity(body))
          case _ => (sig, Impure)
        }

      case Signature(Label.Decreases, Seq(measure, body)) =>
        // TODO: Pureté?
        (sig, codePurity(measure) ++ codePurity(body))

      // TODO: Voir ce qu'on peut faire de plus?
      //        case Signature(Label.MatchExpr(patterns), scrut +: cases) =>
      //          ???

      // TODO: Let of ADT???
      // TODO: Let of ADT???
      // TODO: Let of ADT???
      // TODO: Let of ADT???
      case Signature(Label.Let, Seq(e, body)) =>
        // TODO: Peut-on faire autre chose???
        // TODO: Cette histoire de vd dans lambda???
        //  -> Ah, mais c'est peut-être pour éviter une explosion en cas de lambda inlining?
        //  Hmmm, on devra p-e gérer ça dans le "uncodeOf"? Ou du moins l'opti intermédiaire...
        // TODO: Cette histoire de inline lambda???
        (sig, codePurity(e) ++ codePurity(body))

      case Signature(Label.IfExpr, Seq(cond, thenn, elze)) =>
        val pCond = codePurity(cond)
        val pThen = codePurity(thenn)
        val pElse = codePurity(elze)
        val purity = pCond ++ pThen ++ pElse

        // Note: on check la purity de `else` parce que c'est elle qu'on va dropper
        // TODO: On peut faire des trucs comme ifExpr
        if (pCond.isPure) {
          if (pElse.isPure && cond == trueCode) return (code2sig(thenn), pThen)
          else if (pThen.isPure && cond == falseCode) return (code2sig(elze), pElse)
          else if (thenn == elze) {
            assert(pThen == pElse)
            return (code2sig(thenn), pThen)
          }
        }

        (code2sig(thenn), code2sig(elze)) match {
          case (Signature(Label.IfExpr, Seq(cond2, thenn2, elze2)), _) if elze == elze2 =>
            val combinedCond = conjunct(Set(cond, cond2))
            val sig2 = Signature(Label.IfExpr, Seq(combinedCond, thenn2, elze2))
            simplifySigTopLvl(sig2, tpe)
          case (_, Signature(Label.IfExpr, Seq(cond2, thenn2, elze2))) if thenn == thenn2 =>
            val combinedCond = simplifiedDisjunction(Set(cond, cond2))
            val sig2 = Signature(Label.IfExpr, Seq(combinedCond, thenn2, elze2))
            simplifySigTopLvl(sig2, tpe)
          case _ => (sig, purity)
        }

      case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
        val purity = codePurity(e)
        isConstructor(e, adt, id) match {
          case Some(b) if purity.isPure => (b2sig(b), Pure)
          case Some(b) =>
            (Signature(Label.Let, Seq(e, b2c(b))), purity)
          case None => (sig, purity)
        }

      case Signature(Label.ADTSelector(_, ctor, sel), Seq(e)) =>
        // TODO: Cette histoire de ADT invariant?
        // TODO: Cette histoire de ADT invariant?
        // TODO: Cette histoire de ADT invariant?
        // TODO: approche un peu différente de SWP
        code2sig(e) match {
          // TODO: A-t-on de toute façon id == ctor.id ?
          case Signature(Label.ADT(id, _), args) =>
            assert(id == ctor.id, "woot? les ids ne correspondent pas!!!!")
            val index = ctor.definition.selectorID2Index(sel)
            // Les args qui ne sont pas pures doivent être let-bound
            val toBeBound = args.zipWithIndex.filter { case (c, i) => i != index && !codePurity(c).isPure }.map(_._1)
            // Le résultat de la selection
            val selRes = args(index)
            val resWithBdgs = toBeBound.foldRight(selRes) {
              case (arg, rest) =>
                val p = codePurity(arg) ++ codePurity(rest)
                updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
            }
            (code2sig(resWithBdgs), codePurity(resWithBdgs))
          case _ =>
            // TODO: Cette histoire de ADT invariant?
            (sig, codePurity(e) ++ (if (opts.assumeChecked) Pure else Impure)) // TODO: Ok avec assumeChecked?
        }

      case Signature(Label.ADT(id, tps), args) =>
        // TODO: Cette histoire de ADT invariant?
        // TODO: Cette histoire de ADT invariant?
        // TODO: Cette histoire de ADT invariant?

        // Simplification de ADT(base.fld1, base.fld2, etc.) en base si base est de meme nature que l'adt construite
        val ctor: TypedADTConstructor = getConstructor(id, tps)
        val bases: Seq[Code] = ctor.fields.zip(args.map(code2sig)).collect {
          case (vd, Signature(Label.ADTSelector(_, ctor2, sel), Seq(base)))
            if vd.id == sel && ctor == ctor2 => base
        }
        val newAdt = bases match {
          case base +: basesRest
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
                val p = codePurity(arg) ++ codePurity(rest)
                updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
            }
            code2sig(resWithBdgs)
          case _ =>
            sig
        }
        val argsPurity = fold(args.map(codePurity))
        // TODO: Commentaire au sujet de opts.assumeChecked || !isImpureExpr(newAdt)
        //  en gros, les base.fld1 seront marqué pures si isCtor est vrai, donc l'adt invariant
        //  peut venir a disparaitre si on marque cette ADT(..) comme pur aussi
        // TODO: Mais puisqu'on a `base`, on doit bien avoir l'adt invariant (que ce soit par param ou ailleurs) non?
        val consingPurity = {
          if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
          else Impure
        }
        (newAdt, argsPurity ++ consingPurity)

      case Signature(Label.Tuple, args) => (sig, fold(args.map(codePurity)))
      case Signature(Label.TupleSelect(ii), Seq(e)) =>
        val i = ii - 1
        (code2sig(e), codePurity(e)) match {
          case (Signature(Label.Tuple, args), p) =>
            // Comme pour ADTSelector, les args qui ne sont pas pures doivent être let-bound
            val toBeBound = args.zipWithIndex.filter { case (c, j) => i != j && !codePurity(c).isPure }.map(_._1)
            // let _ = toBeBound in args(i)
            val resWithBdgs = toBeBound.foldRight(args(i)) {
              case (arg, rest) =>
                val p = codePurity(arg) ++ codePurity(rest)
                updateCodesSig(Signature(Label.Let, Seq(arg, rest)), p, tpe)
            }
            (code2sig(resWithBdgs), p)
          case (_, p) => (sig, p)
        }

      case Signature(Label.Lambda(_), Seq(_)) => (sig, Pure)

      case Signature(Label.Application, callee +: args) =>
        // TODO: On suppose que si callee est originellement let-bound, alors son occurence est de 1 (pr éviter explosion d'inlining)
        // TODO: Opti
        // TODO: Pureté?
        (sig, assmChkPurity ++ fold(args.map(codePurity)))

      case Signature(Label.Choose(tpe), Seq(`trueCode`)) if hasInstance(tpe) == Some(true) => (sig, Pure)
      case Signature(Label.Choose(_), Seq(_)) => (sig, Impure) // TODO: simp choose
      case Signature(Label.Forall(_), Seq(pred)) => (sig, codePurity(pred)) // TODO: simp forall

      case Signature(Label.Equals | Label.GreaterEquals | Label.LessEquals, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (trueSig, Pure) }
        else (sig, p1 ++ p2)

      case Signature(Label.LessThan | Label.GreaterThan, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (falseSig, Pure) }
        else (sig, p1 ++ p2)

      case Signature(Label.UMinus, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.UMinus, Seq(e2)) => (code2sig(e2), codePurity(e2))
          case _ => (sig, codePurity(e))
        }

      case Signature(Label.Plus, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
        else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
        else (sig, p1 ++ p2)

      case Signature(Label.Minus, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (zeroSig, Pure) }
        else (sig, p1 ++ p2)

      case Signature(Label.Times, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); (zeroSig, Pure) }
        else if (e1 == one) { assert(p1.isPure); (code2sig(e2), p2) }
        else if (e2 == one) { assert(p2.isPure); (code2sig(e1), p1) }
        else (sig, p1 ++ p2)

      case Signature(Label.Division | Label.Remainder | Label.Modulo, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (opts.assumeChecked && e2 != zero && e1 == zero && p2.isPure) { assert(p1.isPure); (zeroSig, Pure) }
        else if (opts.assumeChecked && e2 != zero && e1 == e2 && p1.isPure) { assert(p2.isPure); (oneSig, Pure) }
        else (sig, assmChkPurity ++ p1 ++ p2)

      case Signature(Label.BVNot, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.BVNot, Seq(e2)) => (code2sig(e2), codePurity(e2))
          case _ => (sig, codePurity(e))
        }

      case Signature(Label.BVAnd, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (code2sig(e1), Pure) }
        else if ((e1 == zero && p2.isPure) || (e2 == zero && p1.isPure)) { assert(p1.isPure && p2.isPure); (zeroSig, Pure) }
        else (sig, p1 ++ p2)

      case Signature(Label.BVOr, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (code2sig(e1), Pure) }
        else if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
        else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
        else (sig, p1 ++ p2)

      case Signature(Label.BVXor, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e1 == e2 && p1.isPure) { assert(p2.isPure); (zeroSig, Pure) }
        else if (e1 == zero) { assert(p1.isPure); (code2sig(e2), p2) }
        else if (e2 == zero) { assert(p2.isPure); (code2sig(e1), p1) }
        else (sig, p1 ++ p2)

      case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
        val p1 = codePurity(e1)
        val p2 = codePurity(e2)
        if (e2 == zero) {assert(p2.isPure); (code2sig(e1), p1) }
        else (sig, p1 ++ p2)

      case Signature(Label.BVNarrowingCast(_) | Label.BVWideningCast(_) | Label.BVUnsignedToSigned | Label.BVSignedToUnsigned, Seq(e)) =>
        (sig, codePurity(e))

      case Signature(Label.FiniteSet(_) | Label.SetAdd | Label.ElementOfSet | Label.SubsetOf | Label.SetIntersection | Label.SetUnion | Label.SetDifference
                   | Label.FiniteArray(_) | Label.LargeArray(_, _) | Label.ArraySelect | Label.ArrayUpdated | Label.ArrayLength, children) =>
        // TODO: On peut faire mieux (voir si cela en faut la peine)
        (sig, fold(children.map(codePurity)))

      case Signature(Label.Annotated(_), Seq(e)) => (sig, codePurity(e))

      case Signature(Label.Error(_, _), Seq()) => (sig, assmChkPurity) // TODO: Pureté ok? Car dans SWP et isImpure, aucune mention de Error...
      case Signature(Label.NoTree(_), Seq()) => (sig, assmChkPurity) // TODO: Ditto...

      case sig =>
        println("simplifySigTopLevel: What is this: "+sig)
        ???
    }
  }

  def updateCodesSig(sig: Signature, purity: Purity, tpe: Type): Code = {
    sig2code.get(sig) match {
      case Some(c) =>
        assert(codePurity(c) == purity, s"${codePurity(c)} != $purity")
        assert(codeTpe(c) == tpe, s"${codeTpe(c)} != $tpe")
        c
      case None =>
        val newCode = Code.fromInt(sig2code.size)
        assert(!code2sig.contains(newCode))
        sig2code += sig -> newCode
        code2sig += newCode -> sig
        codeTpe += newCode -> tpe
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
      val lhsConj = conjunct(env.conditions)
      val rhsLhsConj = conjunct(Set(lhsConj, rhs))
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
      updateCodesSig(Signature(Label.IsConstructor(adt, ofId), Seq(c)), codePurity(c), BooleanType())
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

  def sigOfIndexedVar(bIx: BinderIx, tpe: Type)(using env: OEnv): Signature = mkIxVar(bIx.toVarIx(env.scopeLevel), tpe)

  // TODO: Peut-on subst des let-bound à leur définition même si ces defs sont impures?
  def sigOfVariable(v: Variable)(using env: OEnv): (Signature, Purity) = {
    // Check if `v` is let-bound *and* that we can use the signature/code of the definition of v
    env.letDef.get(v).filter(_._2).map((c, _) => (code2sig(c), codePurity(c)))
      // Check if `v` is bound to a lambda, choose forall or let (for which the substitution was forbidden)
      .orElse(env.bound.get(v).map(bIx => (sigOfIndexedVar(bIx, v.getType), Pure)))
      .getOrElse((mkFreeVar(v), Pure))
  }

  def conjunct(conj: Set[Code])(using OEnv): Code = negCodeOf(negatedConjunction(conj))

  def negatedConjunction(conj: Set[Code])(using OEnv): Code= {
    // TODO: Caching?
    simplifiedDisjunction(conj.map(negCodeOf))
  }

  def codeOfIntLit(lit: BigInt, tpe: Type)(using OEnv): Code = codeOf(intLitOfType(lit, tpe))

  def intLitOfType(lit: BigInt, tpe: Type): Expr = tpe match {
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

  case class RevEnv(letDefs: Map[BinderIx, Code],
                    revLetDefs: Map[Code, BinderIx],
                    scopeLevel: Int,
                    inLambda: Boolean,
                    noPC: Boolean) {
    def withLetBound(df: Code): RevEnv = withLetBounds(Seq(df))

    def withLetBounds(dfs: Seq[Code]): RevEnv = withLetBoundsAndIndices(dfs)._1

    def withLetBoundsAndIndices(dfs: Seq[Code]): (RevEnv, Seq[(BinderIx, Code)]) = {
      val indices = dfs.zipWithIndex.map((c, i) => BinderIx.fromScopeLevel(scopeLevel + i) -> c)
      val newRenv = RevEnv(
        letDefs ++ indices.toMap,
        revLetDefs ++ dfs.zipWithIndex.map((c, i) => c -> BinderIx.fromScopeLevel(scopeLevel + i)).toMap,
        scopeLevel + dfs.size,
        inLambda,
        noPC && dfs.forall(codePurity(_).isPure))
      (newRenv, indices)
    }

    def withOpenBoundsAndIndices(nbBounds: Int): (RevEnv, Seq[BinderIx]) =
      (copy(scopeLevel = scopeLevel + nbBounds), (scopeLevel until (scopeLevel + nbBounds)).map(BinderIx.fromScopeLevel))

    def withOpenBounds(nbBounds: Int): RevEnv = withOpenBoundsAndIndices(nbBounds)._1

    def withPC: RevEnv = copy(noPC = false)
    def withinLambda: RevEnv = copy(inLambda = true)
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty, Map.empty, 0, false, true)
  }

  case class Count(occurrences: Int, inLambda: Boolean, containsLambda: Boolean, noPC: Boolean) {
    def ++(other: Count): Count =
      Count(occurrences + other.occurrences,
        inLambda || other.inLambda,
        containsLambda || other.containsLambda,
        noPC && other.noPC)
  }

  case class Counts(cts: Map[BinderIx, Count]) {
    def of(ix: BinderIx): Count = cts.getOrElse(ix, Count(0, false, false, true))

    def ++(other: Counts): Counts =
      Counts((cts.keySet ++ other.cts.keySet)
        .map(ix => ix -> (of(ix) ++ other.of(ix)))
        .toMap)

    def -(ix: BinderIx): Counts = Counts(cts - ix)
    def --(ixs: Set[BinderIx]): Counts = Counts(cts -- ixs)

    // TODO: Ok?
    // Si le ix a ces counts là, le résultat de la subst par ix
    def replaced(ix: BinderIx, replacedCounts: Counts): Counts = {
      assert(!replacedCounts.cts.contains(ix))
      val ixCt = of(ix)
      if (ixCt.occurrences == 0) return Counts(cts - ix)

      def replaced(candIx: BinderIx): Count = {
        val currCnt = of(candIx)
        val replCnt = replacedCounts.of(candIx)
        if (replCnt.occurrences == 0) currCnt
        else currCnt ++ Count(ixCt.occurrences * replCnt.occurrences,
          ixCt.inLambda || replCnt.inLambda,
          ixCt.containsLambda || replCnt.containsLambda,
          ixCt.noPC && replCnt.noPC)
      }

      Counts(((cts.keySet ++ replacedCounts.cts.keySet) - ix)
        .map(candIx => candIx -> replaced(candIx))
        .toMap)
    }
  }

  object Counts {
    def empty: Counts = Counts(Map.empty)
  }

  case class Holed(expr: Map[BinderIx, Expr] => Expr, holes: Set[BinderIx]) {
    def plugged(ix: BinderIx, e: Expr): Holed = {
      // TODO: Dire que les non-holes sont ignoré
      // TODO: Devrait-on qd même supprimer les es qui ne sont pas des trous (pour eviter interference avec plus bas que soi)?
      // assert(holes.contains(ix), s"$ix not contained in ${holes.toSeq.sorted}")
      // TODO: Hmmm, ça n'a pas de sens? Ou bien?
      Holed.chkd(subst => expr(subst.updated(ix, e)), holes - ix)
    }

    def plugged(es: Map[BinderIx, Expr]): Holed = {
      // TODO: Dire que les non-holes sont ignoré
      // TODO: Devrait-on qd même supprimer les es qui ne sont pas des trous (pour eviter interference avec plus bas que soi)?
      // assert(es.keySet.subsetOf(holes), s"${es.keySet.toSeq.sorted} not a subset of ${holes.toSeq.sorted}")
      // TODO: Ok?
      Holed.chkd(subst => expr(subst ++ es), holes -- es.keySet)
    }

    def plugged(ix: BinderIx, other: Holed): Holed = {
      assert(!other.holes.contains(ix), s"Other ${other.holes.toSeq.sorted} contains $ix")
      Holed.chkd({ subst =>
        // TODO: Ok?
        expr(subst.updated(ix, other.expr(subst)))
      }, (holes ++ other.holes) - ix)
    }
  }

  object Holed {
    def const(e: Expr): Holed = Holed.chkd(_ => e, Set.empty)

    def ofOne(ix: BinderIx): Holed = Holed.chkd(_(ix), Set(ix))

    def combined(holeds: Seq[Holed])(recons: Seq[Expr] => Expr): Holed =
      Holed.chkd({ subst =>
        val exprs = holeds.map(_.expr(subst))
        recons(exprs)
      }, holeds.flatMap(_.holes).toSet)

    def chkd(expr: Map[BinderIx, Expr] => Expr, holes: Set[BinderIx]): Holed = Holed({ subst =>
      assert(holes.subsetOf(subst.keySet), s"${holes.toSeq.sorted} not a subset of ${subst.keys.toSeq.sorted}")
      expr(subst)
    }, holes)
  }

  case class RevRes(holed: Holed, counts: Counts) {
    def countOf(ix: BinderIx): Count = counts.of(ix)

    def plugged(ix: BinderIx, e: Expr): RevRes = RevRes(holed.plugged(ix, e), counts - ix)

    def plugged(es: Map[BinderIx, Expr]): RevRes = RevRes(holed.plugged(es), counts -- es.keySet)

//    def pluggedTrimmed(es: Map[BinderIx, Expr]): RevRes = RevRes(holed.plugged(es), counts -- es.keySet)

    def plugged(ix: BinderIx, other: RevRes): RevRes = {
      assert(!other.holed.holes.contains(ix))
      assert(!other.counts.cts.contains(ix))
      RevRes(holed.plugged(ix, other.holed), counts.replaced(ix, other.counts))
    }
  }

  object RevRes {
    def combined(res: Seq[RevRes])(recons: Seq[Expr] => Expr): RevRes =
      RevRes(Holed.combined(res.map(_.holed))(recons), res.foldLeft(Counts.empty)(_ ++ _.counts)) // TODO: Ok?

    def combined(r1: RevRes)(recons: Expr => Expr): RevRes =
      combined(Seq(r1)) { case Seq(e1) => recons(e1) }

    def combined(r1: RevRes, r2: RevRes)(recons: (Expr, Expr) => Expr): RevRes =
      combined(Seq(r1, r2)) { case Seq(e1, e2) => recons(e1, e2) }

    def combined(r1: RevRes, r2: RevRes, r3: RevRes)(recons: (Expr, Expr, Expr) => Expr): RevRes =
      combined(Seq(r1, r2, r3)) { case Seq(e1, e2, e3) => recons(e1, e2, e3) }
  }

  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  // TODO: Est-ce que le noPC est correct??? Parce que dans lhs + rhs, si lhs a des PC ("non locaux"), alors rhs en aura aussi!!!!
  def uncodeOf(c: Code)(using renv: RevEnv): RevRes = {
    renv.revLetDefs.get(c) match {
      case Some(bIx) =>
        // TODO: Dire pk
        val tpe = codeTpe(c)
        val sig = Signature(Label.IndexedVar(bIx.toVarIx(renv.scopeLevel), tpe), Seq.empty)
        return uncodeOf(updateCodesSig(sig, Pure, tpe))
      case None => ()
    }

    code2sig(c) match {
      case Signature(Label.Var(v), Seq()) => RevRes(Holed.const(v), Counts.empty)
      case Signature(Label.IndexedVar(v, _), Seq()) =>
        val bIx = v.toBinderIx(renv.scopeLevel)
        RevRes(Holed.ofOne(bIx), Counts(Map(bIx -> Count(1, renv.inLambda, false, renv.noPC))))

      case Signature(Label.Let, Seq(cE, cBody)) =>
        val bIx = BinderIx.fromScopeLevel(renv.scopeLevel)
        val resE = uncodeOf(cE)
        // TODO: noPC même pour cE? C'est un peu contraingnant, cela empeche d'inline des impure...
        val noPC = renv.noPC && codePurity(cE).isPure
        val resBody = uncodeOf(cBody)(using renv.withLetBound(cE).copy(noPC = noPC))
        val cntsInBody = resBody.countOf(bIx)
        val canSubstPure = codePurity(cE).isPure &&
          cntsInBody.occurrences <= 1 &&
          (!cntsInBody.inLambda || !cntsInBody.containsLambda)
        /*lazy */val canSubstImpure = !cntsInBody.inLambda && cntsInBody.noPC && cntsInBody.occurrences == 1
        if (canSubstPure || canSubstImpure) resBody.plugged(bIx, resE)
        else {
          val vd = ValDef.fresh("tmp", codeTpe(cE))
          val bodyPlugged = resBody.plugged(bIx, vd.toVariable: Expr)
          // TODO: Counts ok?
          RevRes.combined(resE, bodyPlugged)(Let(vd, _, _))
        }

      // TODO: Combinaison des RevRes (en particulier counts) ok?
      case Signature(Label.MatchExpr(pats), cScrut +: cGuardRhs) =>
        assert(2 * pats.size == cGuardRhs.size)

        def convertPattern(pat: LabelledPattern, vds: Seq[(BinderIx, ValDef)]): Pattern = {
          // TODO: Bouark, yes, hide this monstrosity in this fn...

          var currIx = renv.scopeLevel
          var currVds = vds

          def nextBinder(): Option[ValDef] = {
            if (currVds.isEmpty) None
            else {
              val (ix, vd) = currVds.head
              if (ix == BinderIx.fromScopeLevel(currIx)) {
                currIx += 1
                currVds = currVds.tail
                Some(vd)
              } else {
                currIx += 1
                None
              }
            }
          }

          def rec(pat: LabelledPattern): Pattern = {
            val bdg = nextBinder()
            pat match {
              case LabelledPattern.Wildcard(_) => WildcardPattern(bdg)
              case LabelledPattern.ADT(_, id, tps, sub) => ADTPattern(bdg, id, tps, sub.map(rec))
              case LabelledPattern.TuplePattern(_, sub) => TuplePattern(bdg, sub.map(rec))
              case LabelledPattern.Lit(_, lit) => LiteralPattern(bdg, lit)
              case LabelledPattern.Unapply(_, recs, id, tps, sub) => ???
            }
          }

          rec(pat)
        }

        def processCase(pat: LabelledPattern, cGuard: Code, cRhs: Code): (Pattern, RevRes, RevRes) = {
          val allPats = pat.allPatterns
          // TODO: noPC peut ne pas etre modifie si guard = true et si pattern n'introduit pas de cond supp.
          //            val newRenv = renv.withPC.withLetBounds(allPats.map(_.scrut))
          val (newRenv, scrutsIxs0) = renv.withPC.withLetBoundsAndIndices(allPats.map(_.scrut))
          val scrutsIxs = scrutsIxs0.toMap
          val guard = uncodeOf(cGuard)(using newRenv)
          val rhs = uncodeOf(cRhs)(using newRenv)
          //            val scrutsIxs: Map[Int, Code] = newRenv.letDefs.filter { case (_, c) => allPats.exists(_.scrut == c) }
          val usedScrutsIxs: Seq[BinderIx] = (guard.counts ++ rhs.counts).cts
            .filter { case (ix, cnt) => cnt.occurrences != 0 && scrutsIxs.contains(ix) }
            .keys.toSeq.sorted
          // On remplit les trous introduits grâce à renv.withLetBounds avec les vds qui vont être utilisé comme pattern binding
          val vds = usedScrutsIxs.map(ix => ix -> ValDef.fresh(s"bdg$ix", codeTpe(scrutsIxs(ix))))
          val substs = vds.map { case (ix, vd) => ix -> vd.toVariable }.toMap
          (convertPattern(pat, vds), guard.plugged(substs), rhs.plugged(substs))
        }

        val (guards, rhss) = cGuardRhs.grouped(2).map { case Seq(guard, rhs) => (guard, rhs) }.toSeq.unzip
        // TODO: Ok?
        val scrut = uncodeOf(cScrut)
        val cases = pats.zip(guards).zip(rhss).map {
          case ((labPat, cGuard), cRhs) =>
            // val (pat, guard, rhs) =
            processCase(labPat, cGuard, cRhs)
        }
        // TODO: Ok??? !!! quid des holes introduit pr les bindings qui sont ensuite plugged ??? !!!
        val holes = scrut.holed.holes ++ cases.flatMap { case (_, guard, rhs) => guard.holed.holes ++ rhs.holed.holes }.toSet
        // TODO: Ok??? !!! quid des holes introduit pr les bindings qui sont ensuite plugged ??? !!!
        val counts = scrut.counts ++ cases.foldLeft(Counts.empty) { case (acc, (_, guard, rhs)) => acc ++ guard.counts ++ rhs.counts }

        // TODO: Ok???
        RevRes(Holed.chkd({ subst =>
          val scrutExpr = scrut.holed.expr(subst) // TODO: Et s'il y a des trous holes qui ne sont pas dans scrut/case???
          val casesExpr = cases.map {
            case (pat, guard, rhs) =>
              val guardExpr = guard.holed.expr(subst)
              val rhsExpr = rhs.holed.expr(subst)
              MatchCase(pat, if (guardExpr == BooleanLiteral(true)) None else Some(guardExpr), rhsExpr)
          }
          MatchExpr(scrutExpr, casesExpr)
        }, holes), counts)

      case Signature(Label.Tuple, args) => recHelper(args)(Tuple.apply)
      case Signature(Label.ADT(id, tps), args) => recHelper(args)(ADT(id, tps, _))
      case Signature(Label.ADTSelector(_, _, sel), Seq(recv)) => recHelper(recv)(ADTSelector(_, sel))
      case Signature(Label.FunctionInvocation(id, tps), args) => recHelper(args)(FunctionInvocation(id, tps, _))
      case Signature(Label.Annotated(flags), Seq(e)) => recHelper(e)(Annotated(_, flags))
      case Signature(Label.IsConstructor(_, id), Seq(e)) => recHelper(e)(IsConstructor(_, id))

      case Signature(Label.Assume, Seq(pred, body)) =>
        RevRes.combined(uncodeOf(pred), uncodeOf(body)(using renv.withPC))(Assume.apply)
      case Signature(Label.Assert, Seq(pred, body)) =>
        RevRes.combined(uncodeOf(pred), uncodeOf(body)(using renv.withPC))(Assert(_, None, _))
      case Signature(Label.Require, Seq(pred, body)) =>
        RevRes.combined(uncodeOf(pred), uncodeOf(body)(using renv.withPC))(Require.apply)
      case Signature(Label.Ensuring, Seq(body, pred)) =>
        recHelper(body, pred) { case (body, pred: Lambda) => Ensuring(body, pred) }
      case Signature(Label.Decreases, Seq(measure, body)) =>
        RevRes.combined(uncodeOf(measure), uncodeOf(body)(using renv.withPC))(Decreases.apply)

      case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
        RevRes.combined(uncodeOf(cond), uncodeOf(thn)(using renv.withPC), uncodeOf(els)(using renv.withPC))(IfExpr.apply)
      // TODO: Ok?
      case Signature(Label.Application, all@(callee +: args)) =>
        recHelper(all) { case callee +: args => Application(callee, args) }
      case Signature(Label.Lambda(paramTps), Seq(cBody)) =>
        recHelperOpenBinders(paramTps, cBody)(Lambda.apply)(using renv.withinLambda)
      case Signature(Label.Choose(tpe), Seq(cPred)) =>
        recHelperOpenBinders(Seq(tpe), cPred) { case (Seq(vd), pred) => Choose(vd, pred) }
      case Signature(Label.Forall(paramTps), Seq(cPred)) =>
        recHelperOpenBinders(paramTps, cPred)(Forall.apply)
      case Signature(Label.Or, fst +: rest) =>
        // TODO: Pourrait-on envisager d'ajouter ces assms dans computeSignature (en + d'ocbsl)?
        // Note: due to short-circuiting, the negation of the disjunct are added as we "move" towards the right.
        // So, in `rest`, we have at least the PC `not(fst)` (also see inox.transforms.TransformerWithPC).
        RevRes.combined(uncodeOf(fst) +: rest.map(uncodeOf(_)(using renv.withPC)))(Or.apply)
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
      case Signature(Label.Lit(lit), Seq()) => RevRes(Holed.const(lit), Counts.empty)
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

      case Signature(Label.Error(tpe, descr), Seq()) => RevRes(Holed.const(Error(tpe, descr)), Counts.empty)
      case Signature(Label.NoTree(tpe), Seq()) => RevRes(Holed.const(NoTree(tpe)), Counts.empty)

      case sig =>
        sys.error(s"uncodeOf: what is this: $sig")
    }
  }

  def recHelper(args: Seq[Code])(recons: Seq[Expr] => Expr)(using RevEnv): RevRes = {
    RevRes.combined(args.map(uncodeOf))(recons)
  }

  def recHelper(c1: Code)(recons: Expr => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1)) { case Seq(e1) => recons(e1) }
  def recHelper(c1: Code, c2: Code)(recons: (Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2)) { case Seq(e1, e2) => recons(e1, e2) }
  def recHelper(c1: Code, c2: Code, c3: Code)(recons: (Expr, Expr, Expr) => Expr)(using RevEnv): RevRes =
    recHelper(Seq(c1, c2, c3)) { case Seq(e1, e2, e3) => recons(e1, e2, e3) }

  def recHelperOpenBinders(paramTps: Seq[Type], cBody: Code)(recons: (Seq[ValDef], Expr) => Expr)(using renv: RevEnv): RevRes = {
    val (newRenv, indices) = renv.withOpenBoundsAndIndices(paramTps.size)
    val vds = indices.zip(paramTps).map { case (ix, tpe) => ix -> ValDef.fresh(s"bdg$ix", tpe) }
    val body = uncodeOf(cBody)(using newRenv)
      .plugged(vds.map { case (ix, vd) => ix -> vd.toVariable }.toMap)
    RevRes.combined(body)(recons(vds.map(_._2), _))
  }

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

  def sizeOf(e: Expr): Int = {
    def rec(e: Expr): Int = {
      sizeCache.getOrElse(e, {
        val Operator(es, _) = e
        1 + es.size + es.map(rec).sum
      })
    }
    sizeCache.getOrElseUpdate(e, rec(e))
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  def codePurity(c: Code): Purity = {
    assert(code2sig.contains(c))
    codePurityCache.get(c)
      .map(fromBoolean)
      .getOrElse(Delayed(codeBlockedBy(c)))
  }

  def fnPurity(fn: Identifier)(using env: OEnv): Purity = {
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
          given OEnv = OEnv(Set.empty, Map.empty, 0, Map.empty)
          assert(!visiting.contains(fn))
          assert(!fnBlockedBy.contains(fn))
          assert(!blocking.contains(fn))
          visiting += fn
          val res = codePurity(codeOf(getFunction(fn).fullBody))
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