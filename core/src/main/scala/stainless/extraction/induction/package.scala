/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object induction {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: induction.trees.type = induction.trees }
  }

  def extractor(implicit ctx: inox.Context) = Induction(trees, extraction.trees)
}
