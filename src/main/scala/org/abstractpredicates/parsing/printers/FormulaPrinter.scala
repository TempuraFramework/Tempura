package org.abstractpredicates.parsing.printers

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.helpers.Transforms.EnvTransform
import org.abstractpredicates.smt.SmtLibSolver

import scala.reflect.ClassTag

object FormulaPrinter extends EnvTransform[Core.BoxedExpr, String](using summon[ClassTag[Core.BoxedExpr]], summon[ClassTag[String]]) {

  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(fmla: Core.BoxedExpr): Either[String, String] = {
    val smtlibSolver = SmtLibSolver.SmtLibSolver(typeEnv, interpEnv)
    try 
      Right(smtlibSolver.lower(fmla.e))
    catch
      case e => Left(s"error encountered during printing: ${e.toString}")
  }
}
