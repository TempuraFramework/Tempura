package tempura.smt.modelOperations

import tempura.expression.Core.InterpEnv
import tempura.helpers.Utils.*
import tempura.expression.Syntax.*
import tempura.expression.Core
import tempura.expression.transforms.Visitor
import tempura.smt.SmtSolver

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
