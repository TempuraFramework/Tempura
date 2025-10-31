package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtSolver

trait InterpolationEngine[LT, LVD] {
  // Get the underlying SMT solver
  def solver: SmtSolver.Solver[LT, LVD]
  
  // Compute interpolant between two formulas A and B
  // Returns None if A and B is satisfiable (no interpolant exists)
  // Returns Some(I) where I is the interpolant if A and B is unsatisfiable
  def computeInterpolant(
    formulaA: Core.BoxedExpr, 
    formulaB: Core.BoxedExpr
  ): Option[Core.BoxedExpr]
  
  // Compute sequence interpolant for a list of formulas [A1, A2, ..., An]
  // Returns None if conjunction is satisfiable
  // Returns Some(List(I1,...,In-1)) where each Ii is an interpolant between
  // (A1 and ... and Ai) and (Ai+1 and ... and An)
  def computeSequenceInterpolant(
    formulas: List[Core.BoxedExpr]
  ): Option[List[Core.BoxedExpr]]
  
  // Initialize the interpolation engine with specific logic options
  def initialize(logic: SmtSolver.Logic): Unit
  
  // Reset the internal state
  def reset(): Unit
}