package tempura.transitions

import tempura.smt.SmtSolver.SolverEnvironment
import States.{State, StateGraph, StatePair}
import tempura.expression.Core

import scala.collection.mutable

class LivenessCheck(solverEnv: SolverEnvironment, trs: TransitionSystem) {

  private val solver = solverEnv.solver
  
  private def getPend: Core.Expr[Core.BoolSort] =
    val q = trs.liveProperties.head._2
    val p = trs.liveAssumptions.head._2
    Core.mkAnd(List(p, Core.mkNot(q)))
    
  private def doAllSat(fmla: Core.Expr[Core.BoolSort], vocab: Set[(String, Core.BoxedSort)], n: Int) : List[State] = {
    if n == -1 then {
      solver.push()
      solver.add(List(fmla))
      val result = solver.allSat(vocab)
      solver.pop()
      result.map(x => State(trs.getStateVars, solverEnv, x, dir = States.Direction.Fwd))
    } else {
      solver.push()
      solver.add(List(fmla))
      val result = solver.partialAllSat(vocab, n)
      solver.pop()
      result.map(x => State(trs.getStateVars, solverEnv, x, dir = States.Direction.Fwd))
    }
  }

  private def doAllSat(fmla: Core.Expr[Core.BoolSort], vocab: Set[(String, Core.BoxedSort)]) : List[State] = {
    doAllSat(fmla, vocab, -1)
  }
  
  def sampleLiveTrace(stateGraph: StateGraph) = {
    val pendingWorklist = mutable.Queue.empty[stateGraph.Vertex]
    val liveTraceSubgraph = LabeledGraph[State, StatePair]()
    val visited = mutable.Set.empty[stateGraph.Vertex]
    val pend = getPend
    stateGraph.allNodes foreach {
      x => 
        val xLabel = stateGraph.labelOf(x).get
        if (xLabel.models(pend)) {
          visited.add(x)
          pendingWorklist.enqueue(x)
        }
    }
    
    while (pendingWorklist.nonEmpty) {
      val x = pendingWorklist.dequeue()
      if !visited.contains(x) then {
        stateGraph.successors(x).get foreach {
          y =>
            val xLabel = stateGraph.labelOf(x).get
            val yLabel = stateGraph.labelOf(y).get
            val xyLabel = stateGraph.labelOf(x, y).get

        }
      }
    }
     
  }

  def reachableStates(): StateGraph = {
    val stateGraph = LabeledGraph[State, StatePair]()
    val worklist = mutable.Queue.empty[stateGraph.Vertex]
    val initStates =
      doAllSat(trs.init, trs.getStateVars.map(x => (x.getOriginalName, x.getSort)))
    initStates foreach { state =>
      val vtx = stateGraph.addNode(state)
      worklist.enqueue(vtx)
    }
    while worklist.nonEmpty do {
      val vtx = worklist.dequeue()
      val currLabel = stateGraph.labelOf(vtx).get
      (0 until trs.trans.numTransitions) foreach {
        transitionIndex =>
          val outgoing =
            trs.trans.forwardAllStates(this.solverEnv, currLabel, transitionIndex)
          outgoing foreach {
            e =>
              stateGraph.nodeOfLabel(e._2) match {
                case Some(v) =>
                  if !stateGraph.hasEdge(vtx, v) then
                    stateGraph.addEdge(vtx, v, e._1)
                case None =>
                  val dst = stateGraph.addNode(e._2)
                  stateGraph.addEdge(vtx, dst, e._1)
              }
          }
      }
    }
    stateGraph
  }

}
