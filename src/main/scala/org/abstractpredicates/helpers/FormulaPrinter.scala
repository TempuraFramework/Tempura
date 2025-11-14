package org.abstractpredicates.helpers

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtLibSolver

object FormulaPrinter {

  private final val smtlibSolver = SmtLibSolver.SmtLibSolver(Core.emptyTypeEnv, Core.emptyInterpEnv)

  case class ExprPrinter[S <: Core.Sort[S]](fmla: Core.Expr[S]) {
    def apply(): String =
      smtlibSolver.lower(fmla)
  }

  case class BoxedExprPrinter(fmla: Core.BoxedExpr) {
    def apply(): String =
      smtlibSolver.lower(fmla.e)
  }

}
