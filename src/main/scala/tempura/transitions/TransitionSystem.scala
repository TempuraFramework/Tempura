package tempura.transitions

import cats.implicits.*
import tempura.expression.Core.{BoolSort, InterpEnv, TypeEnv}
import tempura.smt.SmtSolver.*
import tempura.helpers.Utils.*
import tempura.expression.Syntax.*
import tempura.smt.SmtSolver.Result.UNSAT
import tempura.expression.Core
import tempura.expression.transforms.{ExprTransformer, Vocabulary}

import scala.collection.mutable.ListBuffer

class TransitionSystem(val init: Core.Expr[BoolSort], // formula over state variables
                       val trans: TransitionFormula.Transition, // formula over state variables, next-state variables, and internal (transition) variables.
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

  def getTransition: TransitionFormula.Transition = trans

  def getSorts: List[Core.BoxedSort] = this.typeEnv.toList.map(x => x._2)

  def getSortNames: List[String] = this.typeEnv.toList.map(x => x._1)

  def getVars: List[(String, Core.BoxedExpr)] = this.interpEnv.toList

  def getStateVars: Set[StateVariable] = this.trans.getStateVars

  def getTransitionVars: Set[(String, Core.BoxedSort)] = this.trans.getTransitionVars

  def getAllFairAssumptions: Core.Expr[Core.BoolSort] =
    fairAssumptions match {
      case List() => Core.mkFalse
      case List(a) => a._2
      case t => Core.mkOr(t.map(x => x._2))
    }

  def getAllLiveAssumptions: Core.Expr[Core.BoolSort] =
    liveAssumptions match {
      case List() => Core.mkTrue
      case List(a) => a._2
      case t => Core.mkOr(t.map(x => x._2))
    }

  def getAllLiveProperties: Core.Expr[Core.BoolSort] =
    liveProperties match {
      case List() => Core.mkTrue
      case List(a) => a._2
      case t => Core.mkOr(t.map(x => x._2))
    }
}
