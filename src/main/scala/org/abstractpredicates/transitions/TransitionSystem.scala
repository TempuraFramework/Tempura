package org.abstractpredicates.transitions

import cats.implicits.*
import org.abstractpredicates.expression.{Core, Vocabulary}
import org.abstractpredicates.expression.Core.{BoolSort, InterpEnv, TypeEnv}
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.smt.SmtSolver.Result.UNSAT

import scala.collection.mutable.ListBuffer

class TransitionSystem(val stateVars: Set[TimedVariable],
                       val transitionVars: Set[(String, Core.BoxedSort)],
                       val init: Core.Expr[BoolSort], // formula over state variables
                       val trans: List[(String, Core.Expr[Core.BoolSort])], // formula over state variables, next-state variables, and internal (transition) variables.
                       val properties: List[(String, Core.Expr[BoolSort])],
                       val assumptions: List[(String, Core.Expr[BoolSort])],
                       val liveProperties: List[(String, Core.Expr[BoolSort])],
                       val liveAssumptions: List[(String, Core.Expr[Core.BoolSort])],
                       val fairAssumptions: List[(String, Core.Expr[BoolSort])],
                       val theoryAxioms: List[(String, Core.Expr[BoolSort])],
                       val typeEnv: TypeEnv,
                       val interpEnv: InterpEnv) {

  def insertAssumptions(solverEnv: SolverEnvironment): Unit = {
    val solver = solverEnv.solver
    ignore(solver.add(assumptions.map(x => x._2)))
  }

  def sampleTheoryModel(solverEnv: SolverEnvironment): Option[solverEnv.LoweredTerm] = {
    val solver = solverEnv.solver
    solver.push()
    val vocab = this.theoryAxioms.toSet.flatMap(x => Vocabulary(this.interpEnv)(x._2))
    println(s"theory axioms vocabulary: ${vocab.mkString(", ")}")
    solver.add(this.theoryAxioms.map(x => x._2))
    solver.checkSat() match {
      case Result.SAT =>
        solver.getModel match {
          case Some(m) =>
            solver.pop()
            Some(m.asTerm(vocab))
          case None =>
            solver.pop()
            None
        }
      case _ => None
    }
  }

  def getTypeEnv: Core.TypeEnv = this.typeEnv

  def getInterpEnv: Core.InterpEnv = this.interpEnv

  def getInit: Core.Expr[Core.BoolSort] = init

  def getTransition: Core.Expr[Core.BoolSort] =
    this.trans match {
      case List(t) => t._2
      case List() => Core.mkTrue
      case _ => val transitions = this.trans.map(x => x._2)
        Core.mkOr(transitions)

    }

  def getSorts: List[Core.BoxedSort] = this.typeEnv.toList.map(x => x._2)

  def getSortNames: List[String] = this.typeEnv.toList.map(x => x._1)

  def getVars: List[(String, Core.BoxedExpr)] = this.interpEnv.toList

  def getStateVars: Set[TimedVariable] = this.stateVars
}
