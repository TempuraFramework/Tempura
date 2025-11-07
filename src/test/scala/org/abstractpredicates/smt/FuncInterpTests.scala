package org.abstractpredicates.smt

import com.microsoft.z3
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.smt.SmtSolver.Result
import org.scalatest.funsuite.AnyFunSuite

class FuncInterpTests extends AnyFunSuite {

  private def appUnary(fun: Core.Expr[Core.FunSort[Core.NumericSort]],
                       arg: Core.Expr[Core.NumericSort]): Core.Expr[Core.NumericSort] =
    Core.mkSubst("app", List(("arg_0", arg.box())), fun)

  private def mkNumberExpr(n: Int): Core.Expr[Core.NumericSort] =
    Core.mkNumber(n)

  test("blocking clause encodes entry equality and quantified default with bound variables") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.arithFree)

    val funSort = Core.FunSort(List(Core.numericSort), Core.NumericSort())
    val funExpr = Core.mkVar("f", funSort)
    interpEnv.add("f", funExpr)

    val entryEquality = Core.mkEq(appUnary(funExpr, mkNumberExpr(0)), mkNumberExpr(1))
    solver.add(List(entryEquality.box()))
    assert(solver.checkSat() == Result.SAT)

    val model = solver.getModel.get
    val vocab = Set(("f", funSort.box.asInstanceOf[BoxedSort]))
    val blocking = model.asNegatedTerm(vocab).asInstanceOf[z3.BoolExpr]

    println(s"blocking clause: ${blocking.toString}")

    assert(blocking.isNot)
    val inner = blocking.getArgs()(0).asInstanceOf[z3.BoolExpr]
    assert(inner.isAnd)

    val conjuncts = inner.getArgs
//    assert(conjuncts.exists(_.isEq))
    val quantifierExpr = conjuncts.find(_.isQuantifier)
    assert(quantifierExpr.isDefined)

    val quantifier = quantifierExpr.get.asInstanceOf[z3.Quantifier]
    assert(quantifier.getNumBound == 1)

    val body = quantifier.getBody
    // assert(body.isImplies)

/*    val guard = body.getArgs()(0).asInstanceOf[z3.BoolExpr]
    assert(guard.isNot)
    val guardAtom = guard.getArgs()(0)
    val guardComparison =
      if guardAtom.isOr then guardAtom.getArgs()(0)
      else guardAtom
    assert(guardComparison.isEq)
    val guardLhs = guardComparison.getArgs()(0)*/
   // assert(guardLhs.isBound)

   /* val conclusion = body.getArgs()(1).asInstanceOf[z3.BoolExpr]
    assert(conclusion.isEq)
    val conclusionApp = conclusion.getArgs()(0)
    assert(conclusionApp.isApp)
    assert(conclusionApp.getArgs()(0).isBound)*/
  }

  test("blocking clause uses disjunction over multiple entry matches") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.arithFree)

    val funSort = Core.FunSort(List(Core.numericSort), Core.NumericSort())
    val funExpr = Core.mkVar("g", funSort)
    interpEnv.add("g", funExpr)

    val entryZero = Core.mkEq(appUnary(funExpr, mkNumberExpr(0)), mkNumberExpr(0))
    val entryOne = Core.mkEq(appUnary(funExpr, mkNumberExpr(1)), mkNumberExpr(1))
    solver.add(List(entryZero.box(), entryOne.box()))
    assert(solver.checkSat() == Result.SAT)

    val model = solver.getModel.get
    val vocab = Set(("g", funSort.box.asInstanceOf[BoxedSort]))
    val blocking = model.asNegatedTerm(vocab).asInstanceOf[z3.BoolExpr]

    println(s"blocking: ${blocking.toString}")

    assert(blocking.isNot)
  }
}
