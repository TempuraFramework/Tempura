package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core

class ProjectTransitionSystem(transitionSystem: TransitionSystem) {

  private val projectedSorts = Core.emptyTypeEnv

  def projectableSorts(): List[Core.BoxedSort] =
    transitionSystem.getSorts.filter {
      case uSort: Core.UnInterpretedSort => true
      case _ => false
    }

  // returns true if success  
  def projectSort(sortName: String, size: Int): Boolean = {
    assert(size > 0)
    transitionSystem.typeEnv(sortName) match {
      case Some(boxedSort) =>
        boxedSort match {
          case uSort: Core.UnInterpretedSort =>
            // save this sort as an entry in projectedSorts
            this.projectedSorts.add(sortName, uSort)
            // override corresponding entry in the transitionSystem instance
            transitionSystem.typeEnv.add(sortName, Core.FiniteUniverseSort(sortName, size))
            true
          case _ => false
        }
      case _ => false
    }
  }

  // returns true if success 
  def unprojectSort(sortName: String): Boolean = {
    this.projectedSorts.remove(sortName) match {
      case Some(uSort) =>
        this.transitionSystem.typeEnv.add(sortName, uSort)
        true
      case None =>
        false
    }
  }

  def getProjectedSorts: List[(String, Core.BoxedSort)] =
    this.projectedSorts.toList

  def changeProjectionSize(sortName: String, newSize: Int): Boolean = {
    this.projectedSorts(sortName) match {
      case Some(uSort) =>
        uSort match {
          case Core.FiniteUniverseSort(_, size) =>
            ???
          case _ => false
        }
      case None => false
    }
  }

  def projectAll(size: Int): Unit = {
    assert(size > 0)
    this.projectableSorts().map(sort =>
      projectSort(sort.sortName, size)
    )
  }
}
