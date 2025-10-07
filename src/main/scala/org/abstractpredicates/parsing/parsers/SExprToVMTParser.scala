package org.abstractpredicates.parsing.parsers

import org.abstractpredicates.parsing.ast.{ParseTree, Transformer}
import org.abstractpredicates.transitions.TransitionSystem

object SExprToVMTParser extends Transformer[ParseTree, TransitionSystem] {

  override def setInput(a: ParseTree): Unit = {
    this.input = Some(a)
  }

  def transform(a: ParseTree) : Option[TransitionSystem] = ???

  override def transformInput: Option[TransitionSystem] = {
    this.input match {
      case Some(a) => transform(a)
      case None => None
    }
  }
}
