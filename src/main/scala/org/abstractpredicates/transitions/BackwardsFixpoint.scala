package org.abstractpredicates.transitions

import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.{Model, Result, Solver, SolverEnvironment}
import org.abstractpredicates.expression.{Core, VariableRenamer}
import org.abstractpredicates.transitions.States.{State, States}
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.parsing.printers.FormulaPrinter

import scala.collection.mutable.{Map as MMap, Queue as MQueue, Set as MSet}

class BackwardsFixpoint(val trs: TransitionSystem,
                        val solverEnv: SolverEnvironment,
                        val theoryAxioms: List[solverEnv.LoweredTerm], val disambiguate: Boolean) {

  import BackwardsFixpoint.*

  def this(ts: TransitionSystem, s: SolverEnvironment, ta: List[Core.Expr[Core.BoolSort]]) =
    this(ts, s, ta.map(x => s().lower(x)), false)

  val solver: Solver[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl] = solverEnv.solver

  private var currStep: Int = 0

  private var maxSteps: Int = 100

  private val stateGraph: LabeledGraph[States.State, Core.Expr[Core.BoolSort]] = LabeledGraph[States.State, Core.Expr[Core.BoolSort]]()

  private val stateCache: MMap[States.State, Int] = MMap()

  private val worklist: MQueue[(Int, States.State)] = MQueue()

  private val fairEdgesBuf: MSet[(Int, Core.Expr[Core.BoolSort], Int)] = MSet()

  private val ranking: MMap[Int, Int] = MMap()

  private lazy val combinedFairness: Option[Core.Expr[Core.BoolSort]] = {
    trs.fairAssumptions.map(x => x._2) match {
      case Nil => None
      case single :: Nil => Some(single)
      case many => Some(Core.mkAnd(many))
    }
  }

  private def enqueueState(vertexId: Int): Unit =
    stateGraph.labelOf(vertexId).foreach { st =>
      worklist.enqueue((vertexId, st))
    }

  // Perform updating of rankings
  private def relax(vertexId: Int, newDist: Int): Unit = {
    val oldDist = ranking.getOrElse(vertexId, Int.MaxValue)
    if newDist < oldDist then
      ranking.update(vertexId, newDist)
      enqueueState(vertexId)
  }

  /**
   * Initialize the solver with background theory axioms and liveness assumptions.
   * TODO make sure the theory axioms and the background assumptions are not duplicate.
   */
  def initialize(): Unit = {
    // Add theory axioms to solver context (these remain for entire exploration)
    ignore(solver.addTerms(theoryAxioms))
    // Add transition system assumptions (safety assumptions)
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
    stateCache.get(state) match {
      case Some(vertexId) =>
        // State already exists
        vertexId
      case None =>
        // New state: add to graph
        val vertexId = stateGraph.addNode(state)
        stateCache.update(state, vertexId)
        vertexId
    }
  }

  // Initially compute the set of all states satisfying the liveness condition
  def computeLiveStates(): List[Int] = {
    val liveFormula = trs.liveProperties.map(x => x._2) match {
      case List(single) => single
      case List() =>
        println("Warning: No liveness assertions defined, using 'true' (all states are live)")
        Core.mkTrue
      case _ =>
        failwith("error: cannot handle multiple liveness properties for the same transition system instance yet")
    }
    println(s"starting to compute live states... \n\n > liveFormula: ${FormulaPrinter(trs.typeEnv, trs.interpEnv)(liveFormula)} \n\n")
    val liveModels = computeAllSat(liveFormula)

    if liveModels.isEmpty then {
      println("Warning: No live states found")
      List()
    } else {
      println(s"Found ${liveModels.size} live states")

      liveModels.map { model =>
        val state = State(trs.stateVars, solverEnv, model)
        val vertexId = addStateToGraph(state)
        relax(vertexId, 0)
        vertexId
      }
    }
  }

  // Given a state representing the next-state,
  // create a conjunction of equalities over the next-state variables that describes the state.
  private def buildNextStateConstraints(state: State): Core.Expr[Core.BoolSort] = {
    val constraints = trs.stateVars.toList.flatMap { tvar =>
      val origName = tvar.getOriginalName
      val nextName = tvar.getNextState
      val sort = tvar.getSort
      state.model.valueOf(origName, sort.sort).map(
        constraint =>
          println(s"   > next-state constraint of ${nextName}: ${constraint}")
          Core.mkEq(Core.mkVar(nextName, sort), constraint))
    }
    println(s"next-state constraints: ${constraints.map(x => FormulaPrinter(trs.typeEnv, trs.interpEnv)(x))}")
    if constraints.isEmpty then
      Core.mkTrue
    else
      Core.mkAnd(constraints)
  }

  private def computePredecessors(state: State) = {
    val nextStateConstraints = buildNextStateConstraints(state)
    val predecessorQuery = Core.mkAnd(List(trs.getTransition, nextStateConstraints))
    println(s"predecessor query: ${FormulaPrinter(trs.typeEnv, trs.interpEnv)(predecessorQuery)} \n\n")
    val allModels = computeAllSat(predecessorQuery)
    //allModels.filter(model => !stateCache.contains(modelToState(model))) // TODO
    allModels
  }

  private def modelToState(model: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl]): State = {
    State(trs.stateVars, solverEnv, model)
  }

  def backwardStep(vertexId: Int, state: State): Unit = {
    val currentRank = ranking.getOrElse(vertexId, Int.MaxValue)
    if currentRank == Int.MaxValue then return

    println(s"Exploring state ${vertexId} backwards at step ${currStep} (rank=$currentRank)")

    val predecessorModels = computePredecessors(state)
    println(s"  Found ${predecessorModels.size} unique predecessors")

    predecessorModels.foreach { predModel =>
      val predState = modelToState(predModel)
      val edge =
        if stateCache.contains(predState) then {
          val predVertexId = stateCache(predState)
          println(s"  Predecessor of ${vertexId}: ${predVertexId} (previously added)")
          stateGraph.labelOf(predVertexId, vertexId) match {
            case Some(_) => (predVertexId, trs.getTransition, vertexId)
            case None =>
              println(s"   adding edge from ${vertexId} to ${predVertexId}")
              val edgeOpt = stateGraph.addEdge(predVertexId, vertexId, trs.getTransition) // TODO: correct edge weight
              edgeOpt.getOrElse((predVertexId, trs.getTransition, vertexId))
          }
        } else {
          val predVertexId = addStateToGraph(predState)
          println(s"  Predecessor of ${vertexId}: ${predVertexId}")
          println(s"      Predecessor model Z3: ${predState.model.toString}")
          println(s"      Predecessor model: ${predState.toString}  \n ---------> \n Current model: ${state.toString}")
          val edgeOpt = stateGraph.addEdge(predVertexId, vertexId, trs.getTransition) // TODO: correct edge weight
          edgeOpt.getOrElse((predVertexId, trs.getTransition, vertexId))
        }
      
      val fair = isFairEdge(predState, state)
      if fair then fairEdgesBuf.addOne(edge)

      if currentRank != Int.MaxValue then
        val edgeCost = if fair then 1 else 0
        val candidate = currentRank + edgeCost
        relax(edge._1, candidate)
    }
  }

  def explore(): Unit = {
    currStep = 0

    while worklist.nonEmpty && (currStep < maxSteps || maxSteps < 0) do {
      val (vertexId, state) = worklist.dequeue()
      println(s"explore: Exploring vertex ${vertexId}")
      println(s"explore: State: ${state.toString}")
      backwardStep(vertexId, state)
      currStep += 1
    }
    if worklist.nonEmpty then {
      println(s"Warning: Exploration stopped at step ${currStep} (reached maxSteps=${maxSteps})")
      println(s"         ${worklist.size} states remain unexplored on the worklist")
    } else {
      println(s"Exploration complete: visited ${ranking.size} states in ${currStep} steps")
    }
  }

  def run(): LabeledGraph[State, Core.Expr[Core.BoolSort]] = {
    initialize()
    println(" ** backwardsFixpoint: starting ... ")
    val liveVertices = computeLiveStates()
    println(s" ** LIVE STATES ** (${liveVertices.size} total)")
    liveVertices.foreach(x => println(s"vertex ${x} --- state ${this.stateGraph.labelOf(x).toString}"))
    println(" ****** LIVE STATES END *****")
    if liveVertices.isEmpty then {
      println("No live states found - cannot explore")
    } else {
      explore()
    }
    stateGraph
  }

  /**
   * Check if the initial states can reach any live states.
   */
  def checkLivenessReachable(): Boolean = {
    // Compute initial states
    solver.push()
    solver.add(List(trs.init))
    val initModels = solver.allSat(trs.stateVars.map((x: TimedVariable) => (x.getOriginalName, x.getSort)))
    solver.pop()

    if initModels.isEmpty then {
      println("No initial states found")
      false
    } else {
      // Check if any initial state is in the co-reachable set
      val reachableInitStates = initModels.filter { model =>
        stateCache.contains(modelToState(model))
      }

      if reachableInitStates.nonEmpty then {
        println(s"A live state is reachable: ${reachableInitStates.size}/${initModels.size} initial states can reach live states")
        true
      } else {
        println(s"Non-live trace found: none of the ${initModels.size} initial states can reach live states")
        false
      }
    }
  }


  private def summarizeStatePrimed(state: State): Core.Expr[Core.BoolSort] = {
    val summary = state.summarize
    val renameMap: Map[String, String] =
      trs.stateVars.toList.map(tv => tv.getOriginalName -> tv.getNextState).toMap
    val renamer = new VariableRenamer(renameMap)
    renamer.visit(solverEnv.solver.getInterp)(summary)
  }

  private def isFairEdge(pre: State, post: State): Boolean = combinedFairness match {
    case None => false
    case Some(fairCondition) =>
      val currentSummary = pre.summarize
      val nextPrimed = summarizeStatePrimed(post)
      val exptr = Core.mkAnd(List(currentSummary, nextPrimed))
      solver.push()
      solver.add(List(Core.mkNot(Core.mkImplies(exptr, fairCondition))))
      val result = solver.checkSat()
      solver.pop()
      result == Result.UNSAT
  }

  def getFairEdges: Set[(Int, Core.Expr[Core.BoolSort], Int)] = fairEdgesBuf.toSet

  def getRanking: Map[Int, Int] = ranking.toMap

  def getStatistics: ExplorationStats = {
    ExplorationStats(
      totalStates = stateGraph.allNodes.size,
      totalEdges = stateGraph.allEdges.size,
      explorationSteps = currStep,
      unexploredStates = worklist.size
    )
  }
}

object BackwardsFixpoint {
  /**
   * Statistics collected during backward exploration.
   */
  case class ExplorationStats(
                               totalStates: Int,
                               totalEdges: Int,
                               explorationSteps: Int,
                               unexploredStates: Int
                             ) {
    override def toString: String = {
      s"""Backwards Exploration Statistics:
         |  Total states: $totalStates
         |  Total edges: $totalEdges
         |  Exploration steps: $explorationSteps
         |  Unexplored states: $unexploredStates
         |""".stripMargin
    }
  }
}
