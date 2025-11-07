package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.InterpEnv

import scala.collection.mutable

object Vocabulary {

  class VocabularyVisitor extends Visitor {

    private val vocabulary: scala.collection.mutable.Set[(String, Core.BoxedSort)] = scala.collection.mutable.Set()

    override def varVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Core.Var[A]): Core.Expr[A] = {
      vocabulary.add(v.name, v.sort)
      super.varVisitor(env)(v)
    }

    override def macroVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Core.Macro[X]): Core.Expr[Core.FunSort[X]] = {
      vocabulary.add(expr.name, expr.sort)
      super.macroVisitor(env)(expr)
    }
    
    def getVocabulary: Set[(String, Core.BoxedSort)] = vocabulary.toSet
  }

  def apply[S <: Core.Sort[S]](interpEnv: InterpEnv)(expr: Core.Expr[S]): Set[(String, Core.BoxedSort)] =
    val visitor = new VocabularyVisitor()
    visitor.visit(interpEnv)(expr)
    visitor.getVocabulary
}
