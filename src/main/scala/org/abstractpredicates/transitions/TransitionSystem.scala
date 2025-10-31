package org.abstractpredicates.transitions

import cats.implicits.*
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{BoolSort, InterpEnv, TypeEnv}
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.helpers.Utils.*

class TransitionSystem(val stateVars: Set[TimedVariable],
                       val init: Core.Expr[BoolSort], // formula over state variables
                       val trans: Core.Expr[BoolSort], // formula over state variables, next-state variables, and internal (transition) variables.
                       val assertions: List[Core.Expr[BoolSort]],
                       val assumptions: List[Core.Expr[BoolSort]],
                       val liveAssertions: List[Core.Expr[BoolSort]],
                       val liveAssumptions: List[Core.Expr[BoolSort]],
                       val fairness: List[Core.Expr[BoolSort]],
                       val typeEnv: TypeEnv,
                       val interpEnv: InterpEnv) {

  // Next, we need to insert all assumptions into the system.
  def insertAssumptions(solverEnv: SolverEnvironment): Unit = {
    val solver = solverEnv.solver 
    ignore(solver.add(assumptions.map(x => x.box())))
  }

  // Insert liveness asusmptions
  def insertLivenessAssumptions(solverEnv: SolverEnvironment): Unit = {
    val solver = solverEnv.solver 
    ignore(solver.add(liveAssumptions.map(x => x.box())))
  }
  
  def getSorts: List[Core.BoxedSort] = this.typeEnv.toList.map(x => x._2)
  def getSortNames: List[String] = this.typeEnv.toList.map(x => x._1)
  def getVars: List[(String, Core.BoxedExpr)] = this.interpEnv.toList
  def getStateVars: Set[TimedVariable] = this.stateVars
}
