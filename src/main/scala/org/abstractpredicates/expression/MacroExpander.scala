package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.*
import cats.syntax.all.*
import cats.Traverse
import cats.implicits.*

import scala.annotation.tailrec
import scala.reflect.ClassTag

class MacroExpander extends Visitor {

  override def substituteVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Substitute[X]): Core.Expr[X] = {
    visit(env ++@ expr.varBindings.toEnv)(expr.expr) match {
      case Macro(_, _, body) => body
      case _ => expr 
    }
  }

  override def macroVisitor[X <: Core.Sort[X]](env: InterpEnv)(expr: Macro[X]): Core.Expr[Core.FunSort[X]] = {
    val bodyT = visit(env)(expr.expr)
    // Check how many arguments inside macro have been applied.
    expr.vars.partition(x => env(x._1).isDefined) match {
      case (_, List()) => // all arguments have been applied
        Core.mkMacro(expr.name, List(), bodyT) // nullary function
      case (_, args) if args.nonEmpty => // partial application
        Core.mkMacro(expr.name, expr.vars.filter(x => args.contains(x)), expr.expr)
      case _ => // Else case, simply invoke the default visitor as a fallback.
        super.macroVisitor(env)(expr)
    }
  }


  @tailrec
  private final def isFullyExpandedAux(l: LazyList[Core.Expr[? <: Core.Sort[?]]]) : Boolean = {
    l match {
      case a #:: t =>
        a match {
          case Macro(_, _, _) => false
          case _ => isFullyExpandedAux(t)
        }
      case LazyList() =>
        true
    }
  }
  
  //
  // Check if an expression e is fully-expanded, i.e., contains no Macro(...) sub-trees.
  //
  def isFullyExpanded[A <: Core.Sort[A]](e: Core.Expr[A]) : Boolean = {
    isFullyExpandedAux(e.toLazyList)
  }
}
