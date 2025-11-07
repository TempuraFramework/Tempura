package org.abstractpredicates.smt.interpolants

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtInterpolSolver
import org.abstractpredicates.smt.SmtSolver
import org.abstractpredicates.smt.SmtSolver.*
import cats.syntax.*
import cats.implicits.*
import de.uni_freiburg.informatik.ultimate.logic.Annotation
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool

//
// Solver-agnostic interpolation of formulas
// using SMTInterpol as an auxiliary solver
//
class SmtInterpolInterpolation[LT, LVD](
                                         s: SmtSolver.Solver[LT, LVD]
                                       ) extends InterpolationEngine[LT, LVD] {

  private val logLevel: SmtInterpolSolver.LogLevel = SmtInterpolSolver.LogLevel.ERROR
  private val smtInterpolSolver = SmtInterpolSolver.SmtInterpolSolver(s.getTypeEnv, s.getInterp, logLevel)

  override def solver: SolverEnvironment = smtInterpolSolver.box

  override def computeInterpolant(formulaA: Core.Expr[Core.BoolSort], formulaB: Core.Expr[Core.BoolSort]): Option[Core.Expr[Core.BoolSort]] = {
    val smtInterpol = smtInterpolSolver.getSolver
    smtInterpolSolver.push()
    val annotA = Annotation(":named", "fmlaA")
    val annotB = Annotation(":named", "fmlaB")
    val loweredA = smtInterpol.annotate(smtInterpolSolver.lower(formulaA), annotA)
    val loweredB = smtInterpol.annotate(smtInterpolSolver.lower(formulaB), annotB)
    smtInterpol.assertTerm(loweredA)
    smtInterpol.assertTerm(loweredB)
    smtInterpol.checkSat() match {
      case LBool.UNSAT =>
        val itps = smtInterpol.getInterpolants(Array(smtInterpol.term("fmlaA"), smtInterpol.term("fmlaB")))
        smtInterpolSolver.pop()
        if itps.isEmpty then None
        else {
          assert(itps.length == 1)
          smtInterpolSolver.liftTerm(itps(0)).unify(Core.boolSort)
        }
      case _ =>
        smtInterpolSolver.pop()
        None
    }
  }

  override def computeSequenceInterpolant(formulas: List[Core.Expr[Core.BoolSort]]): Option[List[Core.Expr[Core.BoolSort]]] = {
    smtInterpolSolver.push()
    val smtInterpol = smtInterpolSolver.getSolver
    val loweredFormulas = formulas.zipWithIndex.map((formula, i) =>
      val lowered = smtInterpolSolver.lower(formula)
      val annot = Annotation(":named", "fmla_" + i.toString)
      smtInterpol.annotate(lowered, annot)).toArray
    val annots = loweredFormulas.indices.map(i => smtInterpol.term("fmla_" + i.toString))
    loweredFormulas.foreach(x => smtInterpol.assertTerm(x))
    smtInterpol.checkSat() match {
      case LBool.UNSAT =>
        val itps = smtInterpol.getInterpolants(annots.toArray)
        smtInterpolSolver.pop()
        if itps.isEmpty then None else {
          assert(itps.length == formulas.length - 1)
          itps.map(smtInterpolSolver.liftTerm).map(_.unify(Core.boolSort)).toList.traverse(x => x)
        }
      case _ =>
        smtInterpolSolver.pop()
        None
    }
  }

  override def initialize(logic: Logic): Unit = {
    smtInterpolSolver.initialize(logic)
  }

  override def reset(): Unit = smtInterpolSolver.reset()
}
