package tempura.temporal

import CTL.CTLProperty
import CTL.Direction.{Backward, Forward}
import tempura.smt.SmtSolver
import tempura.transitions.States.StateGraph
import tempura.transitions.TransitionSystem

object EG {

  
  def fixpointBody(solverEnv: SmtSolver.SolverEnvironment)(prop: CTLProperty): (CTLProperty, Boolean) = ??? /*{
    val phi = prop.fmla
    val initVtx = prop.dir.init(prop.stateGraph)
    initVtx foreach {
      vtx => 
        val lbl = prop.stateGraph.labelOf(vtx)
        val nextStates = prop.dir.delta(lbl.get)
        nextStates foreach {
          state => 
            prop.stateGraph.nodeOfLabel(state) match {
              case Some(nextVtx) =>
                prop.dir match {
                  case Forward(_, _) =>
                    prop.stateGraph.addEdge(from)
                  case Backward(_, _) =>
                }
            }
        }
    }
  }*/

  def apply(solverEnv: SmtSolver.SolverEnvironment)(prop: CTLProperty): Either[String, CTLProperty] = {
    ???
  }
}
