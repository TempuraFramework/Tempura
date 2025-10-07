package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.*

class VariableRenamer(renameMap: Map[String, String]) extends Visitor {

  override def varVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Var[A]): Core.Expr[A] = {
    renameMap.get(v.name) match {
      case Some(newName) => Var(newName, v.sort)
      case None => v
    }
  }
}
