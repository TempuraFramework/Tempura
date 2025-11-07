package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.failwith
import org.abstractpredicates.smt.Cvc5Solver
import org.abstractpredicates.smt.SmtSolver
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.smt.SmtSolver.SolverEnvironment

import scala.reflect.ClassTag

class Cvc5Interpolation[LT, LVD](s: SmtSolver.Solver[LT, LVD]) extends InterpolationEngine[LT, LVD] {

  private val cvc5Solver = Cvc5Solver.Cvc5Solver(s.getTypeEnv, s.getInterp)

  override def solver: SolverEnvironment = cvc5Solver.box

  // 
  // XXX: CVC5 interpolation interface is phrased positively, assuming that |= A -> B.
  // Thus we need to negate B.
  // In particular, note (A->B) = (not(A) \/ B), so not(A->B) = (A /\ not(B)), 
  // That is, |= A -> B iff (A /\ not(B)) is UNSAT.
  override def computeInterpolant(formulaA: Core.Expr[Core.BoolSort], formulaB: Core.Expr[Core.BoolSort]): Option[Core.Expr[Core.BoolSort]] = {
    val cvc5 = cvc5Solver.getSolver
    val cvc5TM = cvc5Solver.getTermManager
    val fmlaB = cvc5Solver.lower(Core.mkNot(formulaB))
    cvc5Solver.push()
    cvc5.assertFormula(cvc5Solver.lower(formulaA))
    val t = cvc5.getInterpolant(fmlaB)
    if t.toString == "null" then {
      cvc5Solver.pop()
      None
    } else {
      cvc5Solver.pop()
      println(s"gotTerm: ${t}")
      cvc5Solver.liftTerm(t).unify(Core.boolSort) match {
        case Some(lifted) => Some(lifted)
        case None => failwith(s"Err: expected boolean expression from CVC5 but got ${t}")
      }
    }
  }
  
  override def initialize(logic: SmtSolver.Logic): Unit = {
    cvc5Solver.initialize(logic)
  }

  override def reset(): Unit = {
    cvc5Solver.reset()
  }
}
