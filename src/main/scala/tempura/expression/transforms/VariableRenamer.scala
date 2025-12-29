package tempura.expression.transforms

import tempura.expression.Core.*
import tempura.expression.Core

class VariableRenamer(renameMap: Map[String, String]) extends Visitor {

  override def varVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Var[A]): Core.Expr[A] = {
    renameMap.get(v.name) match {
      case Some(newName) => Var(newName, v.sort)
      case None => v
    }
  }
}
