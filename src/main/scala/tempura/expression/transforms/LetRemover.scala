package tempura.expression.transforms

import tempura.expression.Core
import tempura.expression.Core.*

import scala.reflect.ClassTag

// removes let-bindings via substitution
class LetRemover extends Visitor {

  override def substituteVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Substitute[X]): Core.Expr[X] = {
    if expr.attribute == "let" then {
      val newEnv = env ++@ expr.varBindings.toEnv
      super.visit(newEnv)(expr.expr) match {
        case Macro(_, _, body) => body
        case _ => super.substituteVisitor(env)(expr)
      }
    } else super.substituteVisitor(env)(expr)
  }
}
