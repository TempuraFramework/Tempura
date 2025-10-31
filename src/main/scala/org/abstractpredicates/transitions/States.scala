package org.abstractpredicates.transitions

import org.abstractpredicates.abstraction.ConcreteDomain
import org.abstractpredicates.expression.{Core, VariableRenamer}
import org.abstractpredicates.smt.SmtSolver.*

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

    def summarize: Core.Expr[Core.BoolSort] = model.formula()

    def primed: Core.Expr[Core.BoolSort] = {
      val fmla = model.formula()
      val renamer = VariableRenamer(stateVars.map(x => (x.getOriginalName, x.getNextState)).toMap[String, String])
      val fmlaPrimed = renamer.visit(solver.solver.getInterp)(fmla)
      fmlaPrimed
    }
  }

}