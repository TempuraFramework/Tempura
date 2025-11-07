package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.{Core, Vocabulary}
import org.abstractpredicates.smt.SmtSolver
import org.abstractpredicates.smt.SmtSolver.SolverEnvironment
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.failwith
import org.abstractpredicates.smt.modelOperations.Projection

//
// Perform interpolant generation via quantifier elimination.
// Works for any generic solver, as long as the solver itself supports performing QE
// on the corresponding background theory of the formulas passed in.
//
class QEInterpolation[LT, LVD](s: SmtSolver.Solver[LT, LVD]) extends InterpolationEngine[LT, LVD] {

  private val interpolatingSolver = s.fork()


  override def solver: SolverEnvironment = interpolatingSolver.box

  // Want: Given A and B such that A /\ B is UNSAT,
  // find I such that 
  //  (1) I in L(A) intersect L(B), 
  //  (2) A => I,
  //  (3) I /\ B is UNSAT
  // Observe that we can simply take `exists X. A` where X is the set of variables that only appear in A.
  // However, such a formula is quantified so we use some heuristics to try eliminate X entirely from A.
  // Related discussion: Gabbay and Maksimova. Interpolation and Definability. pp. 5.
  override def computeInterpolant(formulaA: Core.Expr[Core.BoolSort], formulaB: Core.Expr[Core.BoolSort]): Option[Core.Expr[Core.BoolSort]] = {
    interpolatingSolver.push()
    interpolatingSolver.add(List(formulaA))
    val result0 = interpolatingSolver.checkSat()
    if result0 == SmtSolver.Result.UNSAT then {
      interpolatingSolver.pop()
      return Some(Core.mkFalse)
    }
    interpolatingSolver.pop()
    interpolatingSolver.add(List(formulaA, formulaB))
    val result = interpolatingSolver.checkSat()
    interpolatingSolver.pop()
    result match {
      case SmtSolver.Result.UNSAT =>
        val vocabA = Vocabulary(interpolatingSolver.getInterp)(formulaA)
        val vocabB = Vocabulary(interpolatingSolver.getInterp)(formulaB)
        val entirelyVocabA = vocabA.diff(vocabB)
        val qItp = Core.mkExists(entirelyVocabA.toList, formulaA)
        interpolatingSolver.push()
        interpolatingSolver.add(List(qItp, formulaB))
        val result1 = interpolatingSolver.checkSat()
        assert(result1 == SmtSolver.Result.UNSAT)
        val itp =
          interpolatingSolver.getUnsatCore match {
            // Heuristic 1: compute (exists X. A(X, Y)) /\ B(Y,Z) and perform projection on the UNSAT core.
            case Some(core) =>
              interpolatingSolver.pop()
              val p = Core.mkAnd(core.formulas().toList)
              val entirelyVocabB = vocabB.diff(vocabA)
              Core.mkExists(entirelyVocabB.toList, p)
            case None =>
              interpolatingSolver.pop()
              interpolatingSolver.push()
              interpolatingSolver.add(List(qItp))
              val result2 = interpolatingSolver.checkSat()
              result2 match {
                case SmtSolver.Result.SAT => // Heuristic 2: directly project on the term (exists X. A(X, Y)).
                  val model = interpolatingSolver.getModel.get
                  val projected = Projection(qItp, interpolatingSolver.box, model, entirelyVocabA)
                  interpolatingSolver.pop()
                  projected
                case SmtSolver.Result.UNKNOWN =>
                  interpolatingSolver.pop()
                  qItp
                case _ =>
                  interpolatingSolver.pop()
                  failwith(s"error: A formula ${formulaA} is not UNSAT, but it implies an UNSAT formula: ${qItp}")
              }
          }
        Some(itp)
      case _ => None
    }
  }

  override def initialize(logic: (SmtSolver.Arith, Boolean, Boolean)): Unit = interpolatingSolver.initialize(logic)

  override def reset(): Unit = {
    interpolatingSolver.reset()
  }
}
