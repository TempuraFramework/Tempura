package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtSolver
import org.abstractpredicates.smt.SmtSolver.Model
import org.abstractpredicates.transitions.Abstractor.TransitionModel
import org.abstractpredicates.expression.Syntax.*

class HelpfulTransitionsMiner[LT, LVD](solver: SmtSolver.Solver[LT, LVD],
                                       stateVars: Set[TimedVariable],
                                       stateGraph: LabeledGraph[States.State, Core.Expr[Core.BoolSort]],
                                       ranking: Map[Int, Int]) {

  def helpfulTransitions: List[TransitionModel[LT, LVD]] = {
    stateGraph.allEdges.toList.flatMap { case (src, _, dst) =>
      (for {
        srcRank <- ranking.get(src)
        dstRank <- ranking.get(dst)
        if srcRank == dstRank + 1
        srcState <- stateGraph.labelOf(src)
        dstState <- stateGraph.labelOf(dst)
      } yield new TransitionModel[LT, LVD](
        solver,
        stateVars,
        Set(srcState.getModel.asInstanceOf[Model[LT, LVD]]), // TODO: fix typechecking issue.
        Set(dstState.getModel.asInstanceOf[Model[LT, LVD]])
      )).toList
    }
  }
}
