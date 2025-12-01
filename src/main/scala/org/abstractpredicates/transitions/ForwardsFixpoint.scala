package org.abstractpredicates.transitions

import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.{Model, Result, Solver, SolverEnvironment}
import org.abstractpredicates.expression.Core
import org.abstractpredicates.transitions.States.{State, States}
import org.abstractpredicates.expression.Syntax.*

import scala.annotation.tailrec
import scala.collection.mutable.{Map as MMap, Queue as MQueue, Set as MSet}

class ForwardsFixpoint(val trs: TransitionSystem,
                       val solverEnv: SolverEnvironment,
                                                 val theoryAxioms: List[Core.Expr[Core.BoolSort]]) {

  import ForwardsFixpoint.*

  val solver: Solver[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl] = solverEnv.solver
  
  // Current exploration step counter
  private var currStep: Int = 0

  // Maximum number of steps to explore (prevents infinite loops)
  private var maxSteps: Int = 100

  private val stateGraph: LabeledGraph[States.State, Core.Expr[Core.BoolSort]] =
    LabeledGraph[States.State, Core.Expr[Core.BoolSort]]()

  private val stateCache: MMap[Core.Expr[Core.BoolSort], Int] = MMap()

  private val worklist: MQueue[(Int, States.State)] = MQueue()

  private val explored: MSet[Int] = MSet()

  def initialize(): Unit = {
    // Add theory axioms to solver context (these remain for entire exploration)
    ignore(solver.add(theoryAxioms.map(x => Core.BoxedExpr.make(x.sort, x))))
    // Add transition system assumptions
    trs.insertAssumptions(solverEnv)
  }

  def setMaxSteps(n: Int): Unit = {
    maxSteps = n
  }

  def getStateGraph: LabeledGraph[States.State, Core.Expr[Core.BoolSort]] = stateGraph

  private def computeAllSat(cond: Core.Expr[Core.BoolSort]) = {
    solver.push()
    solver.add(List(cond))
    val models = solver.allSat(trs.stateVars.map((x: TimedVariable) => (x.getOriginalName, x.getSort)))
    solver.pop()
    models
  }

  private def addStateToGraph(state: State): Int = {
    val stateFormula = summarizeState(state)

    stateCache.get(stateFormula) match {
      case Some(vertexId) =>
        // State already exists
        vertexId

      case None =>
        // New state: add to graph
        val vertexId = stateGraph.addNode(state)
        stateCache.update(stateFormula, vertexId)

        // Add to worklist for exploration
        worklist.enqueue((vertexId, state))

        vertexId
    }
  }

  def initialStates(): List[Int] = {
    val initModels = computeAllSat(trs.init)

    if initModels.isEmpty then {
      println("Warning: No initial states found")
      List()
    } else {
      println(s"Found ${initModels.size} initial states")

      val stateVarsSet = trs.stateVars.toSet
      initModels.map { model =>
        val state = State(stateVarsSet, solverEnv, model)
        addStateToGraph(state)
      }
    }
  }
  
  private def successorStates(state: State) = {
    val stateFormula = state.summarize

    // Build the successor query: current_state ∧ transition_relation
    val successorQuery = Core.mkAnd(List(stateFormula, trs.getTransition))

    // Enumerate all successors
    computeAllSat(successorQuery)
  }

  /**
   * Project a model onto next-state variables to get the successor state.
   * Given a model m that satisfies state(v) ∧ trans(v, v'), we need to
   * extract the v' component.
   *
   * @param model A model satisfying state ∧ trans
   * @return A state corresponding to the next-state portion of the model
   */
  private def projectToNextState(model: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl]): State = {
    val stateVarsSet = trs.stateVars.toSet

    val nextAssignments = trs.stateVars.toList
      .sortBy(_.getNextState)
      .flatMap { tvar =>
        val nextName = tvar.getNextState
        val origName = tvar.getOriginalName
        val sort = tvar.getSort


        model.valueOf(nextName, sort.sort) match {
          case Some(value) =>
            println(s"  *** getting next-state value for ${origName} : ${value.toString}")
            Some(Core.mkEq(Core.mkVar(origName, sort), value))
          case None =>
            // fall back to current value if next-state missing
            model.valueOf(origName, sort.sort).map { current =>
              Core.mkEq(Core.mkVar(origName, sort), current)
            }
        }
      }

    val summary =
      if nextAssignments.isEmpty then Core.mkTrue
      else Core.mkAnd(nextAssignments)

    println(s" ** summary: ${summary.toString}")

    val forked = solverEnv.solver.fork()
    ignore(forked.add(List(summary)))
    val projectedModel =
      if forked.checkSat() == Result.SAT then forked.getModel.getOrElse(model)
      else model

    State(stateVarsSet, solverEnv, projectedModel)
  }

  /**
   * Perform one forward exploration step from a given state vertex.
   * Computes all successors and adds edges to the graph.
   *
   * @param vertexId The vertex to explore from
   * @param state The state associated with the vertex
   */
  def forwardStep(vertexId: Int, state: State): Unit = {
    if explored.contains(vertexId) then {
      // Already explored
      return
    }

    explored.add(vertexId)

    println(s"Exploring state ${vertexId} at step ${currStep}")

    // Compute all successor states
    val successorModels = successorStates(state)

    println(s"  Found ${successorModels.size} successors")

    // For each successor, project to next-state and add to graph
    successorModels.foreach { succModel =>
      val succState = projectToNextState(succModel)
      val succVertexId = addStateToGraph(succState)

      // Add edge labeled with the transition relation
      ignore(stateGraph.addEdge(vertexId, succVertexId, trs.getTransition))
    }
  }

  /**
   * Main exploration loop: BFS over the state space.
   * Continues until worklist is empty or maxSteps is reached.
   */
  def explore(): Unit = {
    currStep = 0

    while worklist.nonEmpty && currStep < maxSteps do {
      val (vertexId, state) = worklist.dequeue()

      forwardStep(vertexId, state)

      currStep += 1
    }

    if worklist.nonEmpty then {
      println(s"Warning: Exploration stopped at step ${currStep} (reached maxSteps=${maxSteps})")
      println(s"         ${worklist.size} states remain unexplored")
    } else {
      println(s"Exploration complete: visited ${explored.size} states in ${currStep} steps")
    }
  }

  /**
   * Run the complete forward fixpoint computation:
   * 1. Initialize solver with theory axioms
   * 2. Compute initial states
   * 3. Explore reachable states via BFS
   *
   * @return The computed state graph
   */
  def run(): LabeledGraph[State, Core.Expr[Core.BoolSort]] = {
    initialize()

    val initVertices = initialStates()

    if initVertices.isEmpty then {
      println("No initial states found - cannot explore")
    } else {
      explore()
    }

    stateGraph
  }

  /**
   * Check if a given property holds in all reachable states.
   *
   * @param property The property formula (over state variables)
   * @return true if property holds in all reachable states, false otherwise
   */
  def checkInvariant(property: Core.Expr[Core.BoolSort]): Boolean = {
    val violatingStates = stateGraph.allNodes.filter { vertexId =>
      stateGraph.labelOf(vertexId) match {
        case Some(stateLabel) =>
          val stateFormula = summarizeState(stateLabel)

          // Check if state ∧ ¬property is satisfiable
          solver.push()
          solver.add(List(stateFormula, Core.mkNot(property)))
          val result = solver.checkSat()
          solver.pop()

          result == Result.SAT

        case None =>
          false
      }
    }

    if violatingStates.isEmpty then {
      println(s"Invariant holds in all ${stateGraph.allNodes.size} reachable states")
      true
    } else {
      println(s"Invariant violated in ${violatingStates.size} states: ${violatingStates.mkString(", ")}")
      false
    }
  }

  /**
   * Get summary statistics about the exploration.
   */
  def getStatistics: ExplorationStats = {
    ExplorationStats(
      totalStates = stateGraph.allNodes.size,
      totalEdges = stateGraph.allEdges.size,
      explorationSteps = currStep,
      unexploredStates = worklist.size
    )
  }

  /**
   * Build a canonical formula summarizing the valuation of current-state variables
   * in the given state. The result only mentions original (non-next) variables.
   */
  private def summarizeState(state: State): Core.Expr[Core.BoolSort] = {
    val eqs = trs.stateVars.toList
      .sortBy(_.getOriginalName)
      .flatMap { tvar =>
        val origName = tvar.getOriginalName
        val sort = tvar.getSort
        state.model.valueOf(origName, sort.sort).map { value =>
          Core.mkEq(Core.mkVar(origName, sort), value)
        }
      }

    if eqs.isEmpty then Core.mkTrue else Core.mkAnd(eqs)
  }

  /**
   * Build a canonical formula from a raw model, extracting only current-state variables.
   */
  private def summarizeModel(model: Model[?, ?]): Core.Expr[Core.BoolSort] = {
    val eqs = trs.stateVars.toList
      .sortBy(_.getOriginalName)
      .flatMap { tvar =>
        val origName = tvar.getOriginalName
        val sort = tvar.getSort
        model.valueOf(origName, sort.sort).map { value =>
          Core.mkEq(Core.mkVar(origName, sort), value)
        }
      }

    if eqs.isEmpty then Core.mkTrue else Core.mkAnd(eqs)
  }
}

object ForwardsFixpoint {
  /**
   * Statistics collected during forward exploration.
   */
  case class ExplorationStats(
    totalStates: Int,
    totalEdges: Int,
    explorationSteps: Int,
    unexploredStates: Int
  ) {
    override def toString: String = {
      s"""Exploration Statistics:
         |  Total states: $totalStates
         |  Total edges: $totalEdges
         |  Exploration steps: $explorationSteps
         |  Unexplored states: $unexploredStates
         |""".stripMargin
    }
  }
}
