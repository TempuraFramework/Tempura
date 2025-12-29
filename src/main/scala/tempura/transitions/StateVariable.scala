package tempura.transitions

import tempura.expression.Core

class StateVariable(originalName: String, nextName: String, sort: Core.BoxedSort) {

  def getOriginalName: String = originalName

  def isNextTimeVariable(t: StateVariable): Boolean =
    nextName == t.getOriginalName

  def getSort: Core.BoxedSort = sort

  def getNextState: String = nextName

  def identity: Core.Expr[Core.BoolSort] = Core.mkEq(Core.mkVar(originalName, sort), Core.mkVar(nextName, sort))

  def skolemized: (String, Core.BoxedSort) = (originalName + "_sk", sort)
  
  override def toString: String =
    originalName

  override def equals(other: Any): Boolean =
    other match {
      case t: StateVariable =>
        this.toString == t.toString
      case _ => false
    }
}
