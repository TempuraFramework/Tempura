package tempura.abstraction

import tempura.transitions.*
import tempura.expression.Syntax.*
import tempura.expression.Core
import tempura.expression.transforms.SortRenamer
import tempura.transitions.TransitionFormula.Transition
import tempura.transitions.{TransformTransitionSystem, TransitionSystem}

object ProjectTransitionSystem {

  private final def concretizeSort(t: Core.BoxedSort, size: Int): Core.BoxedSort = {
    Core.FiniteUniverseSort("_" + t.sort.sortName + "_C", size).box
  }

  def apply(projectionScheme: ProjectionScheme, sortAssoc: ProjectionScheme#SortAssoc): TransitionSystem = {
    val typeEnv = projectionScheme.getTransitionSystem.getTypeEnv
    val interpEnv = projectionScheme.getTransitionSystem.getInterpEnv
    val concretizableSorts =
      typeEnv.toList filter {
        x =>
          x._2.sort match
            case Core.UnInterpretedSort(_, _) => true
            case _ => false
      }
    val mapping: List[((String, Core.BoxedSort), (String, Core.BoxedSort))] =
      concretizableSorts map {
        sort =>
          val concreteSort = concretizeSort(sort._2, sortAssoc(sort))
          typeEnv.add(concreteSort.sortName, concreteSort)

          ((sort._1, concreteSort), (concreteSort.sortName, sort._2))
      }
    val (sortToConcreteSortL, concreteSortToSortL) = mapping.unzip
    val (sortToConcreteSort, concreteSortToSort) = (sortToConcreteSortL.toMap, concreteSortToSortL.toMap)
    val newTs = TransformTransitionSystem(projectionScheme.getTransitionSystem, SortRenamer(sortToConcreteSort))
    newTs
  }
}
