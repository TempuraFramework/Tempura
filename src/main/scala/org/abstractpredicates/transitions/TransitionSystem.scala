package org.abstractpredicates.transitions

import cats.implicits.*
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{BoolSort, InterpEnv, TypeEnv}
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.expression.Syntax.*

class TransitionSystem(val stateVars: Set[TimedVariable],
                       val init: Core.Expr[BoolSort], // formula over state variables
                       val trans: List[(String, Core.Expr[Core.BoolSort])], // formula over state variables, next-state variables, and internal (transition) variables.
                       val properties: List[(String, Core.Expr[BoolSort])],
                       val assumptions: List[(String, Core.Expr[BoolSort])],
                       val liveProperties: List[(String, Core.Expr[BoolSort])],
                       val fairAssumptions: List[(String, Core.Expr[BoolSort])],
                       val typeEnv: TypeEnv,
                       val interpEnv: InterpEnv) {

  def insertAssumptions(solverEnv: SolverEnvironment): Unit = {
    val solver = solverEnv.solver 
    ignore(solver.add(assumptions.map(x => x._2)))
  }

  def getInit: Core.Expr[Core.BoolSort] = init 
  def getTransition : Core.Expr[Core.BoolSort] =
    val transitions = this.trans.map(x => x._2)
    Core.mkOr(transitions)
  
  def getSorts: List[Core.BoxedSort] = this.typeEnv.toList.map(x => x._2)
  def getSortNames: List[String] = this.typeEnv.toList.map(x => x._1)
  def getVars: List[(String, Core.BoxedExpr)] = this.interpEnv.toList
  def getStateVars: Set[TimedVariable] = this.stateVars
}
