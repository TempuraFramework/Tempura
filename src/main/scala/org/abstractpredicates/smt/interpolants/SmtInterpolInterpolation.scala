package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.{SmtInterpolSolver, SmtSolver}
import org.abstractpredicates.smt.SmtSolver.Logic

//
// Solver-agnostic interpolation of formulas
// using SMTInterpol as an auxiliary solver
//
class SmtInterpolInterpolation[LT, LVD](
  s: SmtSolver.Solver[LT, LVD],
  logLevel: SmtInterpolSolver.LogLevel = SmtInterpolSolver.LogLevel.ERROR
) extends InterpolationEngine[LT, LVD] {


  private val smtInterpolSolver = SmtInterpolSolver(s.getTypeEnv, s.getInterp, logLevel)

  // Needed to enable proof production in SmtInterpol
  smtInterpolSolver.getSolver.setOption(":produce-proofs", true)
  smtInterpolSolver.getSolver.setOption(":produce-models", true)


  override def solver: SmtSolver.Solver[LT, LVD] = s

  override def computeInterpolant(formulaA: Core.BoxedExpr, formulaB: Core.BoxedExpr): Option[Core.BoxedExpr] = {
    val smtInterpol = smtInterpolSolver.getSolver
    val loweredA = smtInterpolSolver.lower(formulaA)
    val loweredB = smtInterpolSolver.lower(formulaB)
    val itps = smtInterpol.getInterpolants(Array(loweredA, loweredB))
    if itps.isEmpty then None
    else {
      assert(itps.length == 1)
      Some(smtInterpolSolver.liftTerm(itps(0)))
    }
  }

  override def computeSequenceInterpolant(formulas: List[Core.BoxedExpr]): Option[List[Core.BoxedExpr]] = {
    val smtInterpol = smtInterpolSolver.getSolver
    val loweredFormulas = formulas.map(smtInterpolSolver.lower(_)).toArray
    val itps = smtInterpol.getInterpolants(loweredFormulas)
    if itps.isEmpty then None else {
      assert(itps.length == formulas.length - 1)
      Some(itps.map(smtInterpolSolver.liftTerm).toList)
    }
  }

  override def initialize(logic: Logic): Unit = {
  // TODO: set proof mode
  }

  override def reset(): Unit = smtInterpolSolver.reset()
}
