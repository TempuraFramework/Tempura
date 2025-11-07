package org.abstractpredicates.smt.modelOperations

import org.abstractpredicates.expression.Core.InterpEnv
import org.abstractpredicates.expression.{Core, Visitor}
import org.abstractpredicates.smt.SmtSolver
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.expression.Syntax.*

object Projection {

  //
  // Poor man's model-based projection:
  //
  // Project out a given set of vocabulary `vocab` by evaluating all variables inside `model` for a given `formula`.
  //
  def apply[S <: Core.Sort[S]](formula: Core.Expr[S],
                               solverEnv: SmtSolver.SolverEnvironment,
                               model: SmtSolver.Model[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl],
                               vocab: Set[(String, Core.BoxedSort)]): Core.Expr[S] = {

    val interpEnv = Core.emptyInterpEnv
    val visitor = new Visitor

    vocab.foreach {
      x =>
        ignore(interpEnv.add(x._1, model.evaluate(Core.mkVar(x._1, x._2))))
    }

    visitor.visit(interpEnv)(formula)
  }
}
