package tempura.smt.interpolants

import tempura.expression.Syntax.*
import tempura.expression.Core
import tempura.smt.SmtSolver

trait InterpolationEngine[LT, LVD] {
  // Get the interpolating SMT solver
  def solver: SmtSolver.SolverEnvironment
  
  // Compute interpolant (in the negative sense!) between two formulas A and B
  // Returns None if (A and B) is satisfiable (no interpolant exists)
  // Returns Some(I) where I is the interpolant if A and B is unsatisfiable
  // In particular, A |= I, and (I and B) is UNSAT.
  def computeInterpolant(
    formulaA: Core.Expr[Core.BoolSort],
    formulaB: Core.Expr[Core.BoolSort]
  ): Option[Core.Expr[Core.BoolSort]]
  
  // Compute sequence interpolant for a list of formulas [A1, A2, ..., An]
  // Returns None if conjunction is satisfiable
  // Returns Some(List(I1,...,In-1)) where each Ii is an interpolant between
  // (A1 and ... and Ai) and (Ai+1 and ... and An)
  //
  // Many solvers don't have a sequence interpolation mode, so here's a dumb method for now.
  //
  def computeSequenceInterpolant(formulas: List[Core.Expr[Core.BoolSort]]): Option[List[Core.Expr[Core.BoolSort]]] = {
    if formulas.size < 2 then return None
    val n = formulas.size
    val formulasArr = formulas.toArray
    val prefix = Array.ofDim[Core.Expr[Core.BoolSort]](n)
    val suffix = Array.ofDim[Core.Expr[Core.BoolSort]](n)
    val itps = Array.ofDim[Core.Expr[Core.BoolSort]](n - 1)
    prefix(0) = formulasArr(0)
    suffix(n - 1) = formulasArr(n - 1)
    (1 until n).foreach(i =>
      prefix(i) = prefix(i - 1) /\ formulasArr(i)
    )
    (n - 2 until 0 by -1).foreach(i =>
      suffix(i) = suffix(i + 1) /\ formulasArr(i)
    )
    computeInterpolant(prefix(0), suffix(1)) match {
      case Some(itp) =>
        itps(0) = itp
        (1 until n - 1).foreach(i =>
          itps(i) = computeInterpolant(prefix(i), suffix(i + 1)).get
        )
        Some(itps.toList)
      case None => None
    }
  }


  // Initialize the interpolation engine with specific logic options
  def initialize(logic: SmtSolver.Logic): Unit
  
  // Reset the internal state
  def reset(): Unit
}