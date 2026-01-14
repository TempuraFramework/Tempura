package tempura.abstraction

import tempura.expression.Core
import tempura.expression.Core.BoxedSort
import tempura.transitions.TransitionSystem

class ProjectionScheme(ts: TransitionSystem) {

  type ProjectionSort = (String, BoxedSort)
  type SortAssoc = Map[ProjectionSort, Int]

  private val projectableSorts = (ts.getSorts filter {
    bs =>
      bs.sort match {
        case Core.UnInterpretedSort(_, _) => true
        case _ => false
      }
  } map {
    (bs: Core.BoxedSort) => (bs.sort.sortName, bs)
  }).toSet


  def getTransitionSystem: TransitionSystem = ts

  // returns projectable sorts
  def getProjectableSorts: Set[ProjectionSort] = projectableSorts

  // returns any auxiliary info required for doing the projection
  def configureProjection(s: Set[(ProjectionSort, Int)]): SortAssoc = {
    s.toMap
  }

}
