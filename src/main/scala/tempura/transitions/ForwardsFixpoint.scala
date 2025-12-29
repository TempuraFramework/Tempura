package tempura.transitions

import tempura.smt.SmtSolver.SolverEnvironment
import States.{State, StateGraph, StatePair}
import tempura.expression.Core

import scala.collection.mutable

class ForwardsFixpoint(trs: TransitionSystem, solverEnv: SolverEnvironment, theoryAxioms: List[Core.Expr[Core.BoolSort]]) {


  private val solver = solverEnv.solver

  private def getPend: Core.Expr[Core.BoolSort] =
    val q = trs.liveProperties.head._2
    val p = trs.liveAssumptions match {
      case a :: _ => a._2
      case List() => Core.mkTrue
    }
    Core.mkAnd(List(p, Core.mkNot(q)))

  private def getLive: Core.Expr[Core.BoolSort] =
    trs.liveProperties.head._2

  private def getFair: Core.Expr[Core.BoolSort] =
    trs.fairAssumptions.head._2

  private def doAllSat(fmla: Core.Expr[Core.BoolSort], vocab: Set[(String, Core.BoxedSort)], n: Int): List[State] = {
    if n == -1 then {
      solver.push()
      solver.add(List(fmla))
      val result = solver.allSat(vocab)
      solver.pop()
      result.map(x => State(trs.getStateVars, solverEnv, x, dir = States.Direction.InitFwd))
    } else {
      solver.push()
      solver.add(List(fmla))
      val result = solver.partialAllSat(vocab, n)
      solver.pop()
      result.map(x => State(trs.getStateVars, solverEnv, x, dir = States.Direction.InitFwd))
    }
  }

  private def doAllSat(fmla: Core.Expr[Core.BoolSort], vocab: Set[(String, Core.BoxedSort)]): List[State] = {
    doAllSat(fmla, vocab, -1)
  }

  // Returns a live subgraph and a list of fair edges
  def liveStates(stateGraph: StateGraph): (StateGraph, Set[(StateGraph#Vertex, StateGraph#Vertex)]) = {
    val worklist = mutable.Queue.empty[stateGraph.Vertex]
    val liveSubgraph = LabeledGraph[State, StatePair]()
    val fairEdges = mutable.Set.empty[(StateGraph#Vertex, StateGraph#Vertex)]
    stateGraph.allNodes foreach {
      node =>
        val label = stateGraph.labelOf(node).get
        if label.models(getLive) then {
          worklist.enqueue(node)
          liveSubgraph.addNode(node, label)
        }
    }

    while (worklist.nonEmpty) {
      val succNode = worklist.dequeue()
      stateGraph.predecessors(succNode).get foreach { predNode =>
        val predLabel = stateGraph.labelOf(predNode).get
        if predLabel.models(getPend) then {
          val edgeLabel = stateGraph.labelOf(predNode, succNode).get
          liveSubgraph.addNode(predNode, predLabel)
          liveSubgraph.addEdge(predNode, succNode, edgeLabel)
          if (edgeLabel.isFair(getFair)) {
            fairEdges.add((predNode, succNode))
            println("liveStates: Found fair edge: " + predNode + " -> " + succNode + s" | ${edgeLabel}")
          } else {
            println("liveStates: Found non-fair edge: " + predNode + " -> " + succNode)
          }
        }  else {
          println(s"liveStates: Found non-pending state (${predNode}) ${predLabel}")
        }
      }
    }
    (liveSubgraph, fairEdges.toSet)
  }

  def reachableStates(): StateGraph = {
    val stateGraph = LabeledGraph[State, StatePair]()
    val worklist = mutable.Queue.empty[stateGraph.Vertex]
    val initStates =
      doAllSat(trs.init, trs.getStateVars.map(x => (x.getOriginalName, x.getSort)))
    initStates foreach { state =>
      val vtx = stateGraph.addNode(state)

      println(s"found initial state (${vtx}): ${state}")

      worklist.enqueue(vtx)
    }
    while worklist.nonEmpty do {
      val vtx = worklist.dequeue()

      println(s"visiting ${vtx}")
      val currLabel = stateGraph.labelOf(vtx).get
      (0 until trs.trans.numTransitions) foreach {
        transitionIndex =>
          val outgoing =
            trs.trans.forwardAllStates(this.solverEnv, currLabel, transitionIndex)
          println(s"found ${outgoing.size} outgoing edges for ${vtx}")
          outgoing foreach {
            e =>
              println(s"outgoing state: ${e._2}")

              stateGraph.nodeOfLabel(e._2) match {
                case Some(v) =>
                  println(" ... already in graph")
                  if !stateGraph.hasEdge(vtx, v) then
                    stateGraph.addEdge(vtx, v, e._1)
                case None =>
                  println(" ... new node")
                  val dst = stateGraph.addNode(e._2)
                  stateGraph.addEdge(vtx, dst, e._1)
                  worklist.enqueue(dst)
              }
          }
      }
    }
    stateGraph
  }

}
