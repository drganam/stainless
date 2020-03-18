/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object induction {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: induction.trees.type = induction.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    utils.DebugPipeline("Induction", Induction(trees, trace.trees))
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = trace.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: induction.trees.type } = {
    extraction.phaseSemantics(induction.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: trace.trees.type } = {
    trace.phaseSemantics
  }
}