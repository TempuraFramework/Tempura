package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.InterpEnv
import org.abstractpredicates.expression.Core.*
import scala.reflect.ClassTag

// TODO
class AliasSortCensus extends Visitor {

  private val aliasSorts: scala.collection.mutable.Set[Core.AliasSort[? <: Core.Sort[?]]] = scala.collection.mutable.Set()

  private def detect[X <: Core.Sort[X]](expr: Core.Expr[X]) : Unit = {
    expr.sort match {
      case a: Core.AliasSort[_] =>
        aliasSorts += a
      case _ => ()
    }
  }
  
  override def varVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Var[A]): Core.Expr[A] = {
    detect(v)
    super.varVisitor(env)(v)
  }

  override def constVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Const[A]): Core.Expr[A] = {
    v.sortValue.sort match {
      case a: Core.AliasSort[_] =>
        aliasSorts += a
      case _ => ()
    }
    super.constVisitor(env)(v)
  }

  override def macroVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Macro[X]): Core.Expr[Core.FunSort[X]] = {
    aliasSorts ++=
      expr.vars.map(_._2).collect[Core.AliasSort[? <: Core.Sort[?]]] {
        case a: Core.AliasSort[_] => a
      }
    detect(expr)
    super.macroVisitor(env)(expr)
  }

  override def substituteVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Substitute[X]): Core.Expr[X] = { 
    aliasSorts ++= 
      expr.varBindings.map(_._2.sort).collect[Core.AliasSort[? <: Core.Sort[?]]] {
        case a: Core.AliasSort[_] => a
      }
    detect(expr)
    super.substituteVisitor(env)(expr)
  }

}
