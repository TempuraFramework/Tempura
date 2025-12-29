package tempura.transitions

import tempura.expression.Core.BoxedSort
import tempura.smt.SmtSolver.*
import tempura.expression.Syntax.*
import tempura.helpers.Utils.failwith
import tempura.expression.Core
import tempura.expression.transforms.VariableRenamer
import tempura.helpers.Utils
import tempura.parsing.printers.DotPrinter

import scala.language.postfixOps

object States {

  type StateGraph = LabeledGraph[State, StatePair]

  /**
   * In the forward case:
   *  1. In the initial state, the current-state names are assigned;
   *     2. In every subsequent state, the next-state names are assigned.
   *     3. When composing a state with a transition formula, the current-state names are grounded using the assigned names.
   *
   * In the backward case:
   *  1. In the live state, the current-state names are assigned;
   *     2. In every subsequent state, the current-state names are assigned.
   *     3. When composing a state with a transition formula, the next-state names are grounded using the assigned names.
   *
   */

  enum Direction {
    case Fwd
    case Bwd
    case InitFwd
    case InitBwd
  }

  case class StatePair(transitionVars: Set[(String, Core.BoxedSort)], solverEnv: SolverEnvironment,
                       model: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl]) {
    def getModel: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl] = model

    def summarize: Core.Expr[Core.BoolSort] = {
      val eqs = transitionVars.toList.map {
        case (name, sort) =>
          Core.mkEq(Core.mkVar(name, sort), model.valueOf(name, sort).get)
      }
      if eqs.isEmpty then Core.mkTrue else Core.mkAnd(eqs)
    }

    // Figure out what transition variables took on different values between two transitions
    def difference(other: StatePair): Set[(String, Core.BoxedSort)] = {
      val solver = solverEnv.solver
      transitionVars.filter {
        (name, sort) =>
          solver.push()
          val result = {
            model.evaluate(
              Core.mkEq(Core.mkVar(name, sort), other.model.valueOf(name, sort).get)
            )
          }
          if result == Core.mkTrue then {
            solver.pop()
            false
          } else {
            solver.pop()
            true
          }
      }
    }

    // XXX: This assumes fairCondition is written over transition
    // variables as well. If we resort to the definition of a "fairness condition"
    // over state variables, then we really need to be querying a state to check
    // whether a state's "past fairness variable" holds. That is, in our convention,
    // states that are sink vertices of fair concrete transitions are fair.
    def isFair(fairCondition: Core.Expr[Core.BoolSort]): Boolean = {
      model.evaluate(fairCondition) == Core.mkTrue
    }

    override def hashCode(): Int = transitionVars.hashCode() // TODO: this is really inefficient!

    // whether two transitions are equal
    override def equals(obj: Any): Boolean = {
      obj match {
        case otherStatePair: StatePair =>
          this.transitionVars.equals(otherStatePair.transitionVars) && this.difference(otherStatePair).isEmpty
        case _ => false
      }
    }

    override def toString: String = {
      if this.transitionVars.nonEmpty then
        "[" + this.transitionVars.map {
          (name, sort) =>
            s"${name} = ${model.valueOf(name, sort).get};"
        }.mkString("; ") + "]"
      else "[]"
    }
  }

  case class State(stateVars: Set[StateVariable],
                   solverEnv: SolverEnvironment,
                   model: Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl], dir: Direction) {

    val nameToStateVars: Map[String, Set[StateVariable]] = stateVars.groupBy(_.getOriginalName)

    def getAssignedStateVar(stateVar: StateVariable): (String, BoxedSort) =
      dir match {
        case Direction.InitFwd => (stateVar.getOriginalName, stateVar.getSort)
        case Direction.InitBwd => (stateVar.getOriginalName, stateVar.getSort)
        case Direction.Fwd => (stateVar.getNextState, stateVar.getSort)
        case Direction.Bwd => (stateVar.getOriginalName, stateVar.getSort)
      }

    def getConstraint: Core.Expr[Core.BoolSort] = {
      val vars = this.stateVars.map(x => (x, getAssignedStateVar(x)))
      val constraints = vars.map((stateVar, x) => Core.mkEq(Core.mkVar(stateVar.getOriginalName, x._2.sort), model.valueOf(x._1, x._2.sort).get)).toList
      Core.mkAnd(constraints)
    }

    def models(pred: Core.Expr[Core.BoolSort]): Boolean = {
      val solver = solverEnv.solver
      val fmla = getConstraint
      println(s" | models: constraint is ${fmla}")
      solver.push()
      solver.add(List(fmla /\ pred))
      val result = solver.checkSat()
      solver.pop()
      result == Result.SAT
    }

    override def toString: String = {
      this.stateVars.map(stateVar =>
        val assigned = getAssignedStateVar(stateVar)
        val xSort = assigned._2
        val name = assigned._1
        val model = this.model
        val xVar = Core.mkVar(name, xSort.sort)
        xSort.sort match {
          case Core.ArraySort(Core.BoolSort, range) =>
            val xArr = Core.mkVar(name, Core.ArraySort(Core.BoolSort(), range))
            s"${name} = [true -> ${model.evaluate(xArr @< Core.mkTrue >)}]"
          case Core.ArraySort(Core.FiniteUniverseSort(sortName, sortCard), range) =>
            val sort = Core.FiniteUniverseSort(sortName, sortCard)
            val xArr = Core.mkVar(name, Core.ArraySort(sort, range))
            s"${name} = [${
              (0 until sortCard).map(
                idx =>
                  s"${idx} -> " + model.evaluate(xArr @< Core.mkConst(Core.SortValue.FiniteUniverseValue(idx, sort)) >)
              ).mkString("; \n")
            }]"
          case _ =>
            val value = model.evaluate(Core.mkVar(name, xSort.sort))
            s"${name} = ${value};"
        }
      ).mkString("\n")
    }

    override def canEqual(that: Any): Boolean =
      that match {
        case State => true
        case _ => false
      }


    override def equals(obj: Any): Boolean = {
      obj match {
        case otherState: State =>
          // XXX: it's possible two different direction states are the same. We judge whether states are
          // the same by its valuation, not its direction in search.
          if (!this.stateVars.equals(otherState.stateVars)) then false else {
            val thisModel = this.model
            val thatModel = otherState.model
            this.stateVars.map(x =>
              val thisVar = this.getAssignedStateVar(x)
              val thatVar = otherState.getAssignedStateVar(x)
              thisVar._2.sort match {
                case Core.ArraySort(domSort@Core.FiniteUniverseSort(sortName, sortCard), rangeSort) =>
                  val xVar = Core.mkVar(thisVar._1, Core.arraySort(domSort, rangeSort))
                  val yVar = Core.mkVar(thatVar._1, Core.arraySort(domSort, rangeSort))
                  (0 until sortCard).map(idx =>
                    val c = Core.mkConst(Core.SortValue.FiniteUniverseValue(idx, domSort))
                    thisModel.evaluate(
                      xVar @< c >
                    ) == thatModel.evaluate(
                      yVar @< c >
                    )
                  ).reduce((a, b) => a && b)
                case Core.ArraySort(Core.BoolSort, rangeSort) =>
                  val xVar = Core.mkVar(thisVar._1, Core.arraySort(Core.BoolSort(), rangeSort))
                  val yVar = Core.mkVar(thatVar._1, Core.arraySort(Core.BoolSort(), rangeSort))
                  thisModel.evaluate(xVar @< Core.mkTrue >) == thatModel.evaluate(yVar @< Core.mkTrue >) &&
                    thisModel.evaluate(xVar @< Core.mkFalse >) == thatModel.evaluate(yVar @< Core.mkFalse >)
                case fun@Core.FunSort(domSorts, rangeSort) =>
                  val domain: List[List[Core.BoxedExpr]] =
                    domSorts.map {
                      case Core.BoolSort() => List(Core.mkTrue, Core.mkFalse)
                      case s@Core.FiniteUniverseSort(name, card) =>
                        (0 until card).map(idx => Core.mkConst(Core.SortValue.FiniteUniverseValue(idx, s)).box()).toList
                      case domSort => failwith(s"unsupported domain sort during function input equality comparison ${domSort}")
                    }
                  val p = Utils.cartesianProduct(domain)
                  domain.exists(
                    input =>
                      val zippedInput = input.zipWithIndex.map(x => ("arg_" + x._2.toString, x._1))
                      val outputExprX = Core.mkApp(zippedInput, Core.mkVar(thisVar._1, fun))
                      val outputExprY = Core.mkApp(zippedInput, Core.mkVar(thatVar._1, fun))
                      // thisModel[f(input)] == thatModel[f(input)]
                      thisModel.evaluate(
                        Core.mkEq(
                          outputExprX,
                          thatModel.evaluate(outputExprY)
                        )) == Core.mkTrue
                  )
                case _ =>
                  val xVar = Core.mkVar(thisVar._1, thisVar._2.sort)
                  val yVar = Core.mkVar(thatVar._1, thisVar._2.sort)
                  thisModel.evaluate(Core.mkEq(xVar, thatModel.evaluate(yVar))) == Core.mkTrue
              }
            ).reduce((x, y) => x && y)
          }
        case _ => false
      }
    }

    override def hashCode(): Int = {
      stateVars.hashCode()
    }
  }


  final def stateGraphNodeConfig(trs: TransitionSystem, graph: StateGraph)(x: StateGraph#Vertex): DotPrinter.NodeConfig =
    val st = graph.labelOf(x).get
    if st.models(trs.init) then {
      println(s"DOTPRINTER: INIT STATE ${st}")
      DotPrinter.NodeConfig(DotPrinter.NodeShapes.Triangle, "blue", None)
    } else {
      val liveProps = trs.getAllLiveProperties
      if st.models(liveProps) then {
        DotPrinter.NodeConfig(DotPrinter.NodeShapes.InvTriangle, "green", None)
      } else {
        if st.models(trs.getAllFairAssumptions) then {
          DotPrinter.NodeConfig(DotPrinter.NodeShapes.Box, "red", None)
        } else DotPrinter.defaultNodeConfig
      }
    }

  final def stateGraphEdgeConfig(trs: TransitionSystem, graph: StateGraph)(e: StateGraph#Edge): DotPrinter.EdgeConfig = {
    val fair =
      trs.fairAssumptions match {
        case List() => Core.mkFalse
        case List(a) => a._2
        case t => Core.mkOr(t.map(x => x._2))
      }
    if e._2.isFair(fair) then {
      DotPrinter.EdgeConfig("red", DotPrinter.EdgeStyles.Dashed)
    } else {
      DotPrinter.defaultEdgeConfig
    }
  }
}