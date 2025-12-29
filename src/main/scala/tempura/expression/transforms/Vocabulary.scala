package tempura.expression.transforms

import tempura.expression.Core.InterpEnv
import tempura.expression.Core

import scala.collection.mutable
import scala.collection.mutable.ArrayDeque as Stack

object Vocabulary {

  class VocabularyVisitor extends Visitor {

    private val vocabulary: scala.collection.mutable.Set[(String, Core.BoxedSort)] = scala.collection.mutable.Set()

    private val internalVars: Stack[Set[String]] = new mutable.ArrayDeque()

    override def varVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Core.Var[A]): Core.Expr[A] = {
      if !scopeContains(v.name) then {
        vocabulary.add(v.name, v.sort)
      }

      super.varVisitor(env)(v)
    }

    private def scopeContains(s: String): Boolean =
      internalVars.headOption match {
        case Some(vars) =>
          vars.contains(s)
        case None =>
          false
      }

    private def enterScope(s: Set[String]): Unit = {
      internalVars.headOption match {
        case Some(top) =>
          internalVars.prepend(top ++ s)
        case None =>
          internalVars.prepend(s)
      }
    }

    private def leaveScope(): Unit = {
      internalVars.removeHead()
    }

    override def substituteVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Core.Substitute[X]): Core.Expr[X] = {
      enterScope(expr.varBindings.map(_._1).toSet)
      val result = super.substituteVisitor(env)(expr)
      leaveScope()
      result
    }

    override def forallVisitor(env: InterpEnv)(expr: Core.Forall): Core.Expr[Core.BoolSort] = {
      enterScope(expr.vars.map(_._1).toSet)
      val result = super.forallVisitor(env)(expr)
      leaveScope()
      result
    }

    override def existsVisitor(env: InterpEnv)(expr: Core.Exists): Core.Expr[Core.BoolSort] = {
      enterScope(expr.vars.map(_._1).toSet)
      val result = super.existsVisitor(env)(expr)
      leaveScope()
      result
    }

    override def macroVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Core.Macro[X]): Core.Expr[Core.FunSort[X]] = {
      if !scopeContains(expr.name) then vocabulary.add(expr.name, expr.sort)
      super.macroVisitor(env)(expr)
    }

    def getVocabulary: Set[(String, Core.BoxedSort)] = vocabulary.toSet
  }

  def apply[S <: Core.Sort[S]](interpEnv: InterpEnv)(expr: Core.Expr[S]): Set[(String, Core.BoxedSort)] =
    val visitor = new VocabularyVisitor()
    visitor.visit(interpEnv)(expr)
    visitor.getVocabulary
}
