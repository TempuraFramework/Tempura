package org.abstractpredicates.transitions

import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.{Model, Result, Solver, SolverEnvironment}
import org.abstractpredicates.expression.{Core, VariableRenamer}
import org.abstractpredicates.transitions.States.{State, States}

import scala.collection.mutable.{Map as MMap, Queue as MQueue, Set as MSet}

class BackwardsFixpoint(val trs: TransitionSystem,
                        val solverEnv: SolverEnvironment,
                        val theoryAxioms: List[Core.Expr[Core.BoolSort]]) {

  import BackwardsFixpoint.*

  val solver: Solver[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl] = solverEnv.solver

  private var currStep: Int = 0

  private var maxSteps: Int = 100

  private val stateGraph: LabeledGraph[States.State, Core.Expr[Core.BoolSort]] = LabeledGraph[States.State, Core.Expr[Core.BoolSort]]()

  private val stateCache: MMap[Core.Expr[Core.BoolSort], Int] = MMap()

  private val worklist: MQueue[(Int, States.State)] = MQueue()

  private val fairEdgesBuf: MSet[(Int, Core.Expr[Core.BoolSort], Int)] = MSet()

  private val ranking: MMap[Int, Int] = MMap()

  private lazy val combinedFairness: Option[Core.Expr[Core.BoolSort]] = {
    trs.fairness match {
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
    ignore(solver.add(theoryAxioms.map(x => Core.BoxedExpr.make(x.sort, x))))
    // Add transition system assumptions (safety assumptions)
    trs.insertAssumptions(solverEnv)
    // Add liveness assumptions
    trs.insertLivenessAssumptions(solverEnv)
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

  private def partialAllSat(cond: Core.Expr[Core.BoolSort], n: Int) : List[Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl]] = {
    if n <= 0 then List()
    else {
      solver.push()
      solver.add(List(cond))
      solver.checkSat() match {
        case Result.SAT =>
          val model = solver.getModel.get
          solver.pop()

          // Block this model by adding ¬model.formula() and recurse
          val newCond = cond match {
            case Core.And(subExpr) =>
              Core.mkAnd(Core.mkNot(model.formula()) :: subExpr)
            case _ =>
              Core.mkAnd(List(Core.mkNot(model.formula()), cond))
          }
          model :: partialAllSat(newCond, n - 1)

        case Result.UNSAT =>
          solver.pop()
          List()

        case Result.UNKNOWN =>
          solver.pop()
          failwith(s"partialAllSat: Solver returned UNKNOWN at condition ${cond.toString}")
      }
    }
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
        vertexId
    }
  }

  def computeLiveStates(): List[Int] = {
    val liveFormula = trs.liveAssertions match {
      case Nil =>
        println("Warning: No liveness assertions defined, using 'true' (all states are live)")
        Core.mkTrue
      case single :: Nil => single
      case multiple => Core.mkAnd(multiple)
    }

    val liveModels = computeAllSat(liveFormula)

    if liveModels.isEmpty then {
      println("Warning: No live states found")
      List()
    } else {
      println(s"Found ${liveModels.size} live states")

      val stateVarsSet = trs.stateVars.toSet
      liveModels.map { model =>
        val state = State(stateVarsSet, solverEnv, model)
        val vertexId = addStateToGraph(state)
        relax(vertexId, 0)
        vertexId
      }
    }
  }

  private def buildNextStateConstraints(state: State): Core.Expr[Core.BoolSort] = {
    val constraints = trs.stateVars.toList.flatMap { tvar =>
      val origName = tvar.getOriginalName
      val nextName = tvar.getNextState
      val sort = tvar.getSort
      state.model.valueOf(origName, sort.sort).map(v => Core.mkEq(Core.mkVar(nextName, sort), v))
    }
    if constraints.isEmpty then
      Core.mkTrue
    else
      Core.mkAnd(constraints)
  }

  /**
   * Compute all predecessor states from a given state. */
  private def computePredecessors(state: State) = {
    val nextStateConstraints = buildNextStateConstraints(state)
    val predecessorQuery = Core.mkAnd(List(trs.trans, nextStateConstraints))
    computeAllSat(predecessorQuery)
  }

  private def modelToState(model: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl]): State = {
    val stateVarsSet = trs.stateVars.toSet
    State(stateVarsSet, solverEnv, model)
  }

  def backwardStep(vertexId: Int, state: State): Unit = {
    val currentRank = ranking.getOrElse(vertexId, Int.MaxValue)
    if currentRank == Int.MaxValue then return

    println(s"Exploring state ${vertexId} backwards at step ${currStep} (rank=$currentRank)")

    val predecessorModels = computePredecessors(state)
    println(s"  Found ${predecessorModels.size} predecessors")

    predecessorModels.foreach { predModel =>
      val predState = modelToState(predModel)
      val predVertexId = addStateToGraph(predState)

      val edgeOpt = stateGraph.addEdge(vertexId, predVertexId, trs.trans)
      val fair = isFairEdge(predState, state)
      edgeOpt.foreach { added =>
        if fair then fairEdgesBuf.addOne(added)
      }

      if currentRank != Int.MaxValue then
        val edgeCost = if fair then 1 else 0
        val candidate = currentRank + edgeCost
        relax(predVertexId, candidate)
    }
  }

  def explore(): Unit = {
    currStep = 0

    while worklist.nonEmpty && (currStep < maxSteps || maxSteps < 0) do {
      val (vertexId, state) = worklist.dequeue()
      backwardStep(vertexId, state)
      currStep += 1
    }
    if worklist.nonEmpty then {
      println(s"Warning: Exploration stopped at step ${currStep} (reached maxSteps=${maxSteps})")
      println(s"         ${worklist.size} states remain unexplored")
    } else {
      println(s"Exploration complete: visited ${ranking.size} states in ${currStep} steps")
    }
  }

  def run(): LabeledGraph[State, Core.Expr[Core.BoolSort]] = {
    initialize()
    val liveVertices = computeLiveStates()
    if liveVertices.isEmpty then {
      println("No live states found - cannot explore")
    } else {
      explore()
    }
    stateGraph
  }

  /**
   * Check if a given state can reach a live state.
   */
  def isCoReachable(stateFormula: Core.Expr[Core.BoolSort]): Boolean = {
    stateCache.contains(stateFormula)
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
        val stateFormula = summarizeModel(model)
        isCoReachable(stateFormula)
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

  def getStatistics: ExplorationStats = {
    ExplorationStats(
      totalStates = stateGraph.allNodes.size,
      totalEdges = stateGraph.allEdges.size,
      explorationSteps = currStep,
      unexploredStates = worklist.size
    )
  }

  // Build formula representing a particular state
  private def summarizeState(state: State): Core.Expr[Core.BoolSort] = {
    val eqs = trs.stateVars.toList
      .flatMap { tvar =>
        val origName = tvar.getOriginalName
        val sort = tvar.getSort
        state.model.valueOf(origName, sort.sort).map(value => Core.mkEq(Core.mkVar(origName, sort), value))
      }

    if eqs.isEmpty then Core.mkTrue else Core.mkAnd(eqs)
  }

  /**
   * State formula from a model with only variables we wish to keep track.
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

  private def summarizeStatePrimed(state: State): Core.Expr[Core.BoolSort] = {
    val summary = summarizeState(state)
    val renameMap: Map[String, String] =
      trs.stateVars.toList.map(tv => tv.getOriginalName -> tv.getNextState).toMap
    val renamer = new VariableRenamer(renameMap)
    renamer.visit(solverEnv.solver.getInterp)(summary)
  }

  private def isFairEdge(pre: State, post: State): Boolean = combinedFairness match {
    case None => false
    case Some(fairCondition) =>
      val currentSummary = summarizeState(pre)
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
