package org.abstractpredicates.transitions

import org.abstractpredicates.abstraction.ConcreteDomain
import org.abstractpredicates.expression.{Core, VariableRenamer}
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.helpers.Utils
import org.abstractpredicates.helpers.Utils.failwith

import scala.language.postfixOps

object States {
  trait States[LoweredTerm, LoweredVarDecl](stateVars: Set[TimedVariable], solver: SolverEnvironment) {

    def getStateVars: Set[TimedVariable] = stateVars

    def getSolver: SolverEnvironment = solver

    def getModels: List[Model[LoweredTerm, LoweredVarDecl]]

    def summarize: Core.Expr[Core.BoolSort]
  }

  case class State(stateVars: Set[TimedVariable],
                   solver: SolverEnvironment,
                   model: Model[solver.LoweredTerm, solver.LoweredVarDecl]) {

    def getModel: Model[solver.LoweredTerm, solver.LoweredVarDecl] = model

    def getModels: List[Model[solver.LoweredTerm, solver.LoweredVarDecl]] = List(model)

    def summarize: Core.Expr[Core.BoolSort] = {
      val eqs = stateVars.toList
        .flatMap { tvar =>
          val origName = tvar.getOriginalName
          val sort = tvar.getSort.sort
          model.valueOf(origName, sort).map(value => Core.mkEq(Core.mkVar(origName, sort), value))
        }
      if eqs.isEmpty then Core.mkTrue else Core.mkAnd(eqs)
    }

    def primed: Core.Expr[Core.BoolSort] = {
      val fmla = model.formula()
      val renamer = VariableRenamer(stateVars.map(x => (x.getOriginalName, x.getNextState)).toMap[String, String])
      val fmlaPrimed = renamer.visit(solver.solver.getInterp)(fmla)
      fmlaPrimed
    }

    override def toString: String = {
      stateVars.map(x =>
        val name = x.getOriginalName
        val model = this.getModel
        val xSort = x.getSort.sort
        val xVar = Core.mkVar(name, x.getSort.sort)
        xSort match {
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
            val value = model.evaluate(Core.mkVar(name, x.getSort.sort))
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
          if !this.stateVars.equals(otherState.stateVars) then false else {
            val thisModel = this.getModel
            val thatModel = otherState.getModel
            this.stateVars.map(x =>
              x.getSort.sort match {
                case Core.ArraySort(domSort@Core.FiniteUniverseSort(sortName, sortCard), rangeSort) =>
                  val xVar = Core.mkVar(x.getOriginalName, Core.arraySort(domSort, rangeSort))
                  (0 until sortCard).map(idx =>
                    val c = Core.mkConst(Core.SortValue.FiniteUniverseValue(idx, domSort))
                    thisModel.evaluate(
                      xVar @< c >
                    ) == thatModel.evaluate(
                      xVar @< c >
                    )
                  ).reduce((a, b) => a && b)
                case Core.ArraySort(Core.BoolSort, rangeSort) =>
                  val xVar = Core.mkVar(x.getOriginalName, Core.arraySort(Core.BoolSort(), rangeSort))
                  thisModel.evaluate(xVar @< Core.mkTrue >) == thatModel.evaluate(xVar @< Core.mkTrue >) &&
                    thisModel.evaluate(xVar @< Core.mkFalse >) == thatModel.evaluate(xVar @< Core.mkFalse >)
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
                      val outputExpr = Core.mkApp(zippedInput, Core.mkVar(x.getOriginalName, fun))
                      // thisModel[f(input)] == thatModel[f(input)]
                      thisModel.evaluate(
                        Core.mkEq(
                          outputExpr,
                          thatModel.evaluate(outputExpr)
                        )) == Core.mkTrue
                  )
                case _ =>
                  val xVar = Core.mkVar(x.getOriginalName, x.getSort.sort)
                  thisModel.evaluate(Core.mkEq(xVar, thatModel.evaluate(xVar))) == Core.mkTrue
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

  case class Visualize(state: State, trs: TransitionSystem, solverEnv: SolverEnvironment) {

  }
}