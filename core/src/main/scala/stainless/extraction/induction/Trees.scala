/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package induction

trait Trees extends trace.Trees { self =>

  //case object Induct extends Flag("induct", Seq())
  case object FunEq extends Flag("funEq", Seq())

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    //case ("induct", Seq()) => Induct
    case ("funEq", Seq()) => FunEq
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends trace.Printer {
  protected val trees: Trees
}

trait TreeDeconstructor extends trace.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    //case s.Induct => (Seq(), Seq(), Seq(), (_, _, _) => t.Induct)
    case s.FunEq => (Seq(), Seq(), Seq(), (_, _, _) => t.FunEq)
    case _ => super.deconstruct(f)
  }
}