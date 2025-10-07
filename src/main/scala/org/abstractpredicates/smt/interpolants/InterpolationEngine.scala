package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtSolver

trait InterpolationEngine[LT, LVD] {
  // Get the underlying SMT solver
  def solver: SmtSolver.Solver[LT, LVD]
  
  // Compute interpolant between two formulas A and B
  // Returns None if A ∧ B is satisfiable (no interpolant exists)
  // Returns Some(I) where I is the interpolant if A ∧ B is unsatisfiable
  def computeInterpolant(
    formulaA: Core.BoxedExpr, 
    formulaB: Core.BoxedExpr
  ): Option[Core.BoxedExpr]
  
  // Compute sequence interpolant for a list of formulas [A₁, A₂, ..., Aₙ]
  // Returns None if conjunction is satisfiable
  // Returns Some(List(I₁,...,Iₙ₋₁)) where each Iᵢ is an interpolant between
  // (A₁ ∧ ... ∧ Aᵢ) and (Aᵢ₊₁ ∧ ... ∧ Aₙ)
  def computeSequenceInterpolant(
    formulas: List[Core.BoxedExpr]
  ): Option[List[Core.BoxedExpr]]
  
  // Initialize the interpolation engine with specific logic options
  def initialize(logic: SmtSolver.Logic): Unit
  
  // Reset the internal state
  def reset(): Unit
}