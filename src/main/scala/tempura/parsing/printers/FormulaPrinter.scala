package tempura.parsing.printers

import tempura.expression.Core.{InterpEnv, TypeEnv}
import tempura.cozy.Transforms.*
import tempura.expression.Core
import tempura.smt.SmtLibSolver

import scala.reflect.ClassTag

object FormulaPrinter extends Transform[(Core.TypeEnv, Core.InterpEnv, Core.BoxedExpr), Tuple1[String]] {
  override def apply(args: (Core.TypeEnv, Core.InterpEnv, Core.BoxedExpr)): Either[String, Tuple1[String]] = {
    val (typeEnv, interpEnv, fmla) = (args._1, args._2, args._3)
    val smtlibSolver = SmtLibSolver.SmtLibSolver(typeEnv, interpEnv)
    try 
      Right(Tuple1(smtlibSolver.lower(fmla.e)))
    catch
      case e => Left(s"error encountered during printing: ${e.toString}")
  }

  // user-friendly apply
  def apply(te: Core.TypeEnv, ie: Core.InterpEnv)(e: Core.BoxedExpr) : Either[String, String] =
    apply((te, ie, e)) match {
      case Right(Tuple1(r)) => Right(r)
      case Left(err) => Left(err)
    }
}
