package org.abstractpredicates.parsing.ast

trait Transformer[A, B] {
  protected var input: Option[A] = None

  def setInput(a: A) : Unit
  def transformInput: Option[B]
  def apply(a: A) : Option[B] = {
    this.setInput(a)
    this.transformInput
  }
}
