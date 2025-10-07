package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.helpers.Utils.failwith

import scala.reflect.ClassTag

// Visits the AST and performs some amount of beta-reduction given an environment and substitution.
class Visitor {

  def varVisitor[A <: Sort[A]](env: InterpEnv)(v: Var[A]): Expr[A] = {
    env(v.name) match {
      case Some(a) =>
        a.unify(v.sort) match {
          case Some(b) => b
          case None => failwith("Error: variable " + v.name + s" has different sort in AST (${v.sort}) vs in environment ${a.sort}")
        }
      case None => v
    }
  }

  def constVisitor[A <: Sort[A]](env: InterpEnv)(v: Const[A]): Expr[A] = v

  /*
      case ArraySelect[X, Y](a: Expr[ArraySort[X, Y]], index: Expr[X], sort: ArraySort[X, Y]) extends Expr[Y]*/
  def arraySelectVisitor[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArraySelect[X, Y]): Expr[Y] = {
    val visitedArr = visit(env)(a.a)
    val visitedIdx = visit(env)(a.index)
    visitedArr match {
      case Const[ArraySort[X, Y]] (v: SortValue.ArrayValue[x, y] ) =>
        v.default
      case _ => Core.mkSelect[X, Y](visitedArr, visitedIdx)
    }
  }

  //    case ArrayStore[X, Y](a: Expr[ArraySort[X, Y]], index: Expr[X], value: Expr[Y], sort: ArraySort[X, Y]) extends Expr[ArraySort[X, Y]]
  def arrayStoreVisitor[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArrayStore[X, Y]): Expr[ArraySort[X, Y]] = {
    val visitedArr = visit(env)(a.a)
    val visitedIdx = visit(env)(a.index)
    val visitedValue = visit(env)(a.value)
    Core.mkStore[X, Y](visitedArr, visitedIdx, visitedValue)
  }

  // case Top[X, Y, Z, W](name: String, a: Expr[X], b: Expr[Y], c: Expr[Z], sortA: X, sortB: Y, sortC: Z, sortW: W) extends Expr[W]
  def topVisitor[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z], W <: Sort[W]](env: InterpEnv)(expr: Top[X, Y, Z, W]) = {
    val visitedA = visit(env)(expr.a)
    val visitedB = visit(env)(expr.b)
    val visitedC = visit(env)(expr.c)
    Core.mkTop(expr.name, visitedA, visitedB, visitedC, expr.retSort)
  }

  // case Bop[X, Y, Z](name: String, lhs: Expr[X], rhs: Expr[X], sortLHS: X, sortRHS: Y, sortRet: Z) extends Expr[Z]
  def bopVisitor[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z]](env: InterpEnv)(expr: Bop[X, Y, Z]) = {
    val visitedLHS = visit(env)(expr.lhs)
    val visitedRHS = visit(env)(expr.rhs)
    Core.mkBop(expr.name, visitedLHS, visitedRHS, expr.retSort)
  }
  
  def lopVisitor[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(expr: Lop[X, Y]) = {
    val visitedArgs = expr.subExpr.map(visit(env))
    Core.mkLop(expr.name, visitedArgs, expr.argSort, expr.retSort)
  }

  //     case Uop[X, Y](name: String, subExpr: Expr[X], sortDom: X, sortRange: Y) extends Expr[Y]
  def uopVisitor[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(expr: Uop[X, Y]) = {
    val visitedSubexpr = visit(env)(expr.subExpr)
    Core.mkUop(expr.name, visitedSubexpr, expr.retSort)
  }

  def macroVisitor[X <: Sort[X]](env: InterpEnv)(expr: Macro[X]): Expr[FunSort[X]] = {
    Core.mkMacro(expr.name, expr.vars, visit(env)(expr.expr))
  }

  // Substitute
  // Note that in general, the order of parameters in a function signature doesn't matter;
  // Hence, we convert a varBinding to an environment (order-less) when performing substitution.
  def substituteVisitor[X <: Sort[X]](env: InterpEnv)(expr: Substitute[X]): Expr[X] = {
    val newEnv = env ++@ expr.varBindings.toEnv
    val body = visit(newEnv)(expr.expr)
    body match {
      case Macro(_, _, newBody) => newBody
      case _ => expr
    }
  }
  
  def forallVisitor(env: Core.InterpEnv)(expr: Forall) : Expr[BoolSort] = {
    val body = visit(env)(expr.body)
    Forall(expr.vars, body)
  }
  
  def existsVisitor(env: Core.InterpEnv)(expr: Exists) : Expr[BoolSort] = {
    val body = visit(env)(expr.body)
    Exists(expr.vars, body)
  }
  
  def datatypeConstructorRecognizerVisitor(env: Core.InterpEnv)(expr: DatatypeConstructorRecognizer) : Expr[FunSort[BoolSort]] = {
    val visited = expr.subExpr 
    DatatypeConstructorRecognizer(expr.dt, expr.constructorName, visited)
  }

  def visit[A <: Sort[A]](env: InterpEnv)(expr: Expr[A]): Expr[A] = {
    expr match {
      case s@Var(_, _) => varVisitor(env)(s)
      case s@Const(_) => constVisitor(env)(s)
      case sel@ArraySelect(_, _) => arraySelectVisitor(env)(sel)
      case store@ArrayStore(_, _, _) => arrayStoreVisitor(env)(store)
      case top@Top(_, _, _, _, _) => topVisitor(env)(top)
      case bop@Bop(_, _, _, _) => bopVisitor(env)(bop)
      case uop@Uop(_, _, _) => uopVisitor(env)(uop)
      case lop@Lop(_,_,_,_) => lopVisitor(env)(lop)
      case mac@Macro(_, _, _) => macroVisitor(env)(mac)
      case sub@Substitute(_, _, _) => substituteVisitor(env)(sub)
      case forall@ Forall(_,_) => forallVisitor(env)(forall)
      case exists@ Exists(_, _) => existsVisitor(env)(exists)
      case datatypeConstructorRecognizer: DatatypeConstructorRecognizer => datatypeConstructorRecognizerVisitor(env)(datatypeConstructorRecognizer)
    }
  }
}
