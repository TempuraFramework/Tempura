package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core

class TimedVariable(originalName: String, nextName: String, time: Int, sort: Core.BoxedSort) {

  def subscript(newTime: Int): TimedVariable = {
    TimedVariable(originalName, nextName, newTime, sort)
  }

  def getOriginalName: String = originalName

  def isNextTimeVariable(t: TimedVariable): Boolean =
    nextName == t.getOriginalName

  def getSort: Core.BoxedSort = sort

  def getNextState: String = nextName

  def timeDifference(t: TimedVariable): Option[Int] =
    if t.getOriginalName == this.originalName then
      Some(t.getTimestep - this.time)
    else if t.getOriginalName == this.nextName then
      Some(1)
    else None

  def getTimestep: Int = time
  
  def identity: Core.Expr[Core.BoolSort] = Core.mkEq(Core.mkVar(originalName, sort), Core.mkVar(nextName, sort))

  def skolemized: (String, Core.BoxedSort) = (originalName + "_sk", sort)
  
  override def toString: String =
    originalName + "_" + time

  override def equals(other: Any): Boolean =
    other match {
      case t: TimedVariable =>
        this.toString == t.toString
      case _ => false
    }
}
