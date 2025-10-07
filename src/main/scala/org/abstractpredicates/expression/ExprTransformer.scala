package org.abstractpredicates.expression

import org.abstractpredicates.helpers.Utils.failwith
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Core.BoxedExpr
import org.abstractpredicates.expression.Core.SortValue

import cats.syntax.all.*

class ExprTransformer {

  def varTransformer[A <: Sort[A]](env: InterpEnv)(v: Var[A]): BoxedExpr = {
    env(v.name) match {
      case Some(t: Expr[A]) =>
        t
      case _ => v
    }
  }

  def constTransformer[A <: Sort[A]](env: InterpEnv)(v: Const[A]): BoxedExpr = v

  def arraySelectTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArraySelect[X, Y]): BoxedExpr = {
    val visitedArr = transform(env)(a.a)
    val visitedIdx = transform(env)(a.index)
    visitedArr.unbox match {
      case Const(SortValue.ArrayValue(default, _)) =>
        default.box()
      case _ =>
        visitedArr.sort match {
          case t@Core.ArraySort(_, _) if t.domainSort == visitedIdx.sort =>
            visitedArr.unify(Core.ArraySort(visitedIdx.sort, t.rangeSort)) match {
              case Some(arrExpr) => Core.mkSelect(arrExpr, visitedIdx)
              case None => failwith(s"arraySelectTransformer: got a non-array argument: ${visitedArr}")
            }
          case _ => failwith(s"arraySelectTransformer: got a non-array argument: ${visitedArr}")
        }
    }
  }

  def arrayStoreTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArrayStore[X, Y]): BoxedExpr = {
    val visitedArr = transform(env)(a.a)
    val visitedIdx = transform(env)(a.index)
    val visitedValue = transform(env)(a.value)

    visitedArr.unify(Core.ArraySort(visitedIdx.sort, visitedValue.sort)) match {
      case Some(arrayExpr) =>
        Core.mkStore(arrayExpr, visitedIdx.unbox, visitedValue.unbox)
      case None => failwith(s"arrayStoreTransformer: got a non-array argument: ${visitedArr}")
    }

  }

  def topTransformer[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z], W <: Sort[W]](env: InterpEnv)(expr: Top[X, Y, Z, W]): BoxedExpr = {
    val visitedA = transform(env)(expr.a)
    val visitedB = transform(env)(expr.b)
    val visitedC = transform(env)(expr.c)
    Core.mkTop(expr.name, visitedA, visitedB, visitedC, expr.retSort)
  }

  // case Bop[X, Y, Z](name: String, lhs: Expr[X], rhs: Expr[X], sortLHS: X, sortRHS: Y, sortRet: Z) extends Expr[Z]
  def bopTransformer[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z]](env: InterpEnv)(expr: Bop[X, Y, Z]): BoxedExpr = {
    val visitedLHS = transform(env)(expr.lhs)
    val visitedRHS = transform(env)(expr.rhs)
    Core.mkBop(expr.name, visitedLHS, visitedRHS, expr.retSort)
  }

  //     case Uop[X, Y](name: String, subExpr: Expr[X], sortDom: X, sortRange: Y) extends Expr[Y]
  def uopTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(expr: Uop[X, Y]): BoxedExpr = {
    val visitedSubexpr = transform(env)(expr.subExpr)
    Core.mkUop(expr.name, visitedSubexpr, expr.retSort)
  }


  def lopTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(expr: Lop[X, Y]): BoxedExpr = {
    val visitedArgs = expr.subExpr.map(transform(env)).traverse(x => x.unify(expr.argSort)).getOrElse(failwith(s"lopTransformer: cannot unify arguments when transforming ${expr.toString}"))
    Core.mkLop(expr.name, visitedArgs, expr.argSort, expr.retSort)
  }


  def macroTransformer[X <: Sort[X]](env: InterpEnv)(expr: Macro[X]): BoxedExpr = {
    val newBody = transform(env)(expr.expr)
    Core.mkMacro[newBody.T](expr.name, expr.vars, newBody)
  }

  // Substitute
  // Note that in general, the order of parameters in a function signature doesn't matter;
  // Hence, we convert a varBinding to an environment (order-less) when performing substitution.
  def substituteTransformer[X <: Sort[X]](env: InterpEnv)(expr: Substitute[X]): BoxedExpr = {
    val newEnv = env ++@ expr.varBindings.toEnv
    val body = transform(newEnv)(expr.expr)
    body.unbox match {
      case Macro(_, _, newBody) => newBody
      case _ => expr
    }
  }

  def forallTransformer(env: Core.InterpEnv)(expr: Forall): BoxedExpr = {
    val body = transform(env)(expr.body)

    body.unify(Core.BoolSort()) match {
      case Some(bExpr) => Forall(expr.vars, bExpr)
      case None => failwith(s"forallTransformer: forall body transformed into a non-boolean expression: ${body}")
    }
  }

  def existsVisitor(env: Core.InterpEnv)(expr: Exists): BoxedExpr = {
    val body = transform(env)(expr.body)

    body.unify(Core.BoolSort()) match {
      case Some(bExpr) => Exists(expr.vars, bExpr)
      case None => failwith(s"existsTransformer: exists body transformed into a non-boolean expression: ${body}")
    }
  }

  def datatypeConstructorRecognizerVisitor(env: Core.InterpEnv)(expr: DatatypeConstructorRecognizer): BoxedExpr = {
    val visited = expr.subExpr
    DatatypeConstructorRecognizer(expr.dt, expr.constructorName, visited)
  }


  def transform[A <: Sort[A]](env: InterpEnv)(expr: Expr[A]): BoxedExpr = {
    expr match {
      case s@Var(_, _) => varTransformer(env)(s)
      case s@Const(_) => constTransformer(env)(s)
      case sel@ArraySelect(_, _) => arraySelectTransformer(env)(sel)
      case store@ArrayStore(_, _, _) => arrayStoreTransformer(env)(store)
      case top@Top(_, _, _, _, _) => topTransformer(env)(top)
      case bop@Bop(_, _, _, _) => bopTransformer(env)(bop)
      case uop@Uop(_, _, _) => uopTransformer(env)(uop)
      case lop@Lop(_, _, _, _) => lopTransformer(env)(lop)
      case mac@Macro(_, _, _) => macroTransformer(env)(mac)
      case sub@Substitute(_, _, _) => substituteTransformer(env)(sub)
      case forall@Forall(_, _) => forallTransformer(env)(forall)
      case exists@Exists(_, _) => existsVisitor(env)(exists)
      case datatypeConstructorRecognizer: DatatypeConstructorRecognizer => datatypeConstructorRecognizerVisitor(env)(datatypeConstructorRecognizer)
    }
  }

}
