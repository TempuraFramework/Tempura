package org.abstractpredicates.smt

import io.github.cvc5.Kind
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.*
import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Syntax.*

class Cvc5BackendTests extends AnyFunSuite {

  private def freshSolver() = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    (typeEnv, interpEnv, Cvc5Solver.Cvc5Solver(typeEnv, interpEnv))
  }

  test("cvc5 native interpolation test") {
    import io.github.cvc5._

    val d_tm = new TermManager()
    val d_solver = new Solver(d_tm)

    println("CVC5 Version : " + d_solver.getVersion)
    d_solver.setLogic("QF_LIA")
    d_solver.setOption("produce-interpolants", "true")
    d_solver.setOption("incremental", "false")

    val intSort = d_tm.getIntegerSort
    val zero = d_tm.mkInteger(0)
    val x = d_tm.mkConst(intSort, "x")
    val y = d_tm.mkConst(intSort, "y")
    val z = d_tm.mkConst(intSort, "z")

    // Assumptions for interpolation: x + y > 0 /\ x < 0
    d_solver.assertFormula(d_tm.mkTerm(Kind.GT, d_tm.mkTerm(Kind.ADD, x, y), zero))
    d_solver.assertFormula(d_tm.mkTerm(Kind.LT, x, zero))
    // Conjecture for interpolation: y + z > 0 \/ z < 0
    val conj = d_tm.mkTerm(Kind.OR, d_solver.mkTerm(Kind.GT, d_solver.mkTerm(Kind.ADD, y, z), zero), d_solver.mkTerm(Kind.LT, z, zero))
    // Call the interpolation api, while the resulting interpolant is the output
    val output = d_solver.getInterpolant(conj)

    // We expect the resulting output to be a boolean formula
    assert(output.getSort.isBoolean)

    // try with a grammar, a simple grammar admitting true
    val bsort = d_tm.getBooleanSort
    val truen = d_tm.mkBoolean(true)
    val start = d_tm.mkVar(bsort)
    val g = d_solver.mkGrammar(Array(), Array(start))
    val conj2 = d_tm.mkTerm(Kind.EQUAL, zero, zero)
    g.addRule(start, truen)
    // Call the interpolation api, while the resulting interpolant is the output
    val output2 = d_solver.getInterpolant(conj2, g)
    // interpolant must be true
    assert(output2 == truen)
  }

  test("cvc5 model exposes boolean assignments") {
    val (typeEnv, interpEnv, solver) = freshSolver()

    val x = Core.mkVar("x", Core.BoolSort())
    val y = Core.mkVar("y", Core.BoolSort())
    val z = Core.mkVar("z", Core.BoolSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)
    interpEnv.add("z", z)

    solver.add(List(
      Core.mkAnd(List(x, y)),
      Core.mkNot(z)
    ))

    assert(solver.checkSat() == Result.SAT)

    val modelOpt = solver.getModel
    assert(modelOpt.isDefined, "CVC5 solver should return a model")
    val model = modelOpt.get

    val xValue = model.valueOf("x", Core.BoolSort())
    val yValue = model.valueOf("y", Core.BoolSort())
    val zValue = model.valueOf("z", Core.BoolSort())

    assert(xValue.exists(_.toString.contains("true")), s"x should be true in model, got $xValue")
    assert(yValue.exists(_.toString.contains("true")), s"y should be true in model, got $yValue")
    assert(zValue.exists(_.toString.contains("false")), s"z should be false in model, got $zValue")

    val formula = model.formula()
    assert(formula.unify(Core.BoolSort()).isDefined, "model.formula should be boolean")
  }

  test("cvc5 lowers at-most/at-least constraints") {
    val (_, interpEnv, solver) = freshSolver()

    val b0 = Core.mkVar("b0", Core.BoolSort())
    val b1 = Core.mkVar("b1", Core.BoolSort())
    val b2 = Core.mkVar("b2", Core.BoolSort())

    interpEnv.add("b0", b0)
    interpEnv.add("b1", b1)
    interpEnv.add("b2", b2)

    val b0Var = b0.asInstanceOf[Core.Var[Core.BoolSort]]
    val b1Var = b1.asInstanceOf[Core.Var[Core.BoolSort]]
    val b2Var = b2.asInstanceOf[Core.Var[Core.BoolSort]]

    val atMostOne = Core.mkAtMost(1, List(b0Var, b1Var, b2Var))
    val atLeastOne = Core.mkAtLeast(1, List(b0Var, b1Var, b2Var))

    solver.add(List(
      atMostOne,
      atLeastOne,
      Core.mkEq(b0, Core.mkTrue),
      Core.mkEq(b1, Core.mkFalse),
      Core.mkEq(b2, Core.mkFalse)
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get

    val b0Val = model.valueOf("b0", Core.BoolSort())
    val b1Val = model.valueOf("b1", Core.BoolSort())
    val b2Val = model.valueOf("b2", Core.BoolSort())

    assert(b0Val.exists(_.toString.contains("true")))
    assert(b1Val.exists(_.toString.contains("false")))
    assert(b2Val.exists(_.toString.contains("false")))
  }

  test("cvc5 handles integer division and conditional top expression") {
    val (_, interpEnv, solver) = freshSolver()

    val x = Core.mkVar("x", Core.NumericSort())
    val y = Core.mkVar("y", Core.NumericSort())
    val q = Core.mkVar("q", Core.NumericSort())
    val flag = Core.mkVar("flag", Core.BoolSort())
    val chosen = Core.mkVar("chosen", Core.NumericSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)
    interpEnv.add("q", q)
    interpEnv.add("flag", flag)
    interpEnv.add("chosen", chosen)

    val division = Core.mkEq(q, Core.mkBop("/", x, y, Core.NumericSort()))
    val conditional = Core.mkEq(chosen,
      Core.mkTop("=>", flag, Core.mkNumber(5), Core.mkNumber(3), Core.NumericSort()))

    solver.add(List(
      Core.mkEq(x, Core.mkNumber(9)),
      Core.mkEq(y, Core.mkNumber(2)),
      Core.mkEq(flag, Core.mkFalse),
      division,
      conditional
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get

    val qValue = model.valueOf("q", Core.NumericSort())
    val chosenValue = model.valueOf("chosen", Core.NumericSort())

    assert(qValue.exists(_.toString.contains("4")), s"Expected quotient 4, got $qValue")
    assert(chosenValue.exists(_.toString.contains("3")), s"Expected chosen value 3, got $chosenValue")
  }

  test("cvc5 datatype constructors and recognizers") {
    val (typeEnv, _, solver) = freshSolver()
    val pointCtor = Core.constructor("Point", List(
      ("x", Core.numericSort),
      ("y", Core.numericSort)
    ))
    val pointSort = Core.datatypeSort("Point", List(pointCtor))
    typeEnv.add("Point", pointSort)

    val cvcPoint = solver.defineSort(pointSort.sort)
    val tm = solver.getTermManager
    val datatype = cvcPoint.getDatatype
    val ctor = datatype.getConstructor(0)
    val inst = tm.mkTerm(Kind.APPLY_CONSTRUCTOR, ctor.getTerm, tm.mkInteger(1), tm.mkInteger(2))

    val lifted = solver.liftTerm(inst)
    val expected = Core.mkDatatypeAccessor(
      pointSort.sort,
      Core.instantiatedConstructor(pointCtor, List(Core.mkConst(1).box(), Core.mkConst(2).box()))
    )
    assert(lifted == expected)

    val tester = ctor.getTesterTerm
    val recognizer = tm.mkTerm(Kind.APPLY_TESTER, tester, inst)
    val liftedRecognizer = solver.liftTerm(recognizer)
    val expectedRecognizer = Core.mkDatatypeRecognizer(pointSort.sort, "Point", expected)
    assert(liftedRecognizer == expectedRecognizer)
  }

  test("cvc5 model blocking with asTerm/asNegatedTerm") {
    val (_, interpEnv, solver) = freshSolver()

    val x = Core.mkVar("x", Core.BoolSort())
    interpEnv.add("x", x)

    assert(solver.checkSat() == Result.SAT)
    val model1 = solver.getModel.get
    val value1 = model1.evaluate(x).toString

    solver.addTerms(List(model1.asNegatedTerm()))
    assert(solver.checkSat() == Result.SAT)
    val model2 = solver.getModel.get
    val value2 = model2.evaluate(x).toString
    assert(value1 != value2)

    solver.addTerms(List(model2.asTerm()))
    assert(solver.checkSat() == Result.SAT)
    solver.addTerms(List(model2.asNegatedTerm()))
    assert(solver.checkSat() == Result.UNSAT)
  }
}
