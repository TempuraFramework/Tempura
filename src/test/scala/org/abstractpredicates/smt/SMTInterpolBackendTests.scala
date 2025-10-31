package org.abstractpredicates.smt

import de.uni_freiburg.informatik.ultimate.logic.{FunctionSymbol, Sort, Term}
import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.*

class SMTInterpolBackendTests extends AnyFunSuite {

  test("solve boolean formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)
    assert(typeEnv.getUpdateHook.isDefined)
    assert(interpEnv.getUpdateHook.isDefined)
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
    val model = solver.getModel.get
    println(s"model: ---${model.toString}---\n\n")
    println(s"model.formula:${model.formula()}")
    println(s"solver history: ${solver.getHistory}")
    println(s"type environment history: ${typeEnv.getHistory} ")
    println(s"interp environment history: ${interpEnv.getHistory} ")
    assert(true)
  }

  test("solve array formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)
    val arr = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val i = Core.mkVar("i", Core.NumericSort())
    val v = Core.mkVar("v", Core.NumericSort())
    interpEnv.add("arr", arr)
    interpEnv.add("i", i)
    interpEnv.add("v", v)
    solver.add(List(
      Core.mkEq(Core.mkSelect(arr, i), v),
      Core.mkEq(i, Core.mkConst(0)),
      Core.mkEq(v, Core.mkConst(42))
    ))
    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model: ---${model.toString}---\n\n")
    println(s"model.formula:${model.formula()}")
    assert(true)
  }

  test("boolean-indexed arrays are rejected") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val arr = Core.mkVar("arr", Core.ArraySort(Core.BoolSort(), Core.NumericSort()))
    intercept[UnsupportedOperationException] {
      solver.add(List(Core.mkEq(Core.mkSelect(arr, Core.mkTrue), Core.mkConst(1))))
    }
  }

  test("solve nested arrays with uninterpreted indices") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val idxSort = Core.UnInterpretedSort("Idx", 0)
    typeEnv.add("Idx", idxSort.box)

    val innerArray = Core.mkVar("inner", Core.ArraySort(idxSort, Core.NumericSort()))
    val outerArray = Core.mkVar("outer", Core.ArraySort(idxSort, Core.ArraySort(idxSort, Core.NumericSort())))
    val i1 = Core.mkVar("i1", idxSort)
    val i2 = Core.mkVar("i2", idxSort)
    val val1 = Core.mkVar("val1", Core.NumericSort())
    val val2 = Core.mkVar("val2", Core.NumericSort())

    interpEnv.add("inner", innerArray)
    interpEnv.add("outer", outerArray)
    interpEnv.add("i1", i1)
    interpEnv.add("i2", i2)
    interpEnv.add("val1", val1)
    interpEnv.add("val2", val2)

    solver.add(List(
      Core.mkEq(Core.mkSelect(innerArray, i1), val1),
      Core.mkEq(Core.mkSelect(Core.mkSelect(outerArray, i1), i2), val2)
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"nested array model: ${model.formula()}")
  }

  test("solve array with universal quantifier") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val arr = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val i = Core.mkVar("i", Core.NumericSort())

    interpEnv.add("arr", arr)
    interpEnv.add("i", i)

    val constraint = Core.mkForall(
      List(("i", Core.NumericSort())),
      Core.mkImplies(
        Core.mkGt(i, Core.mkConst(100)),
        Core.mkGe(Core.mkSelect(arr, i), Core.mkConst(10))
      )
    )

    solver.add(List(constraint))
    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model: ${model.toString}")
    println(s"model.formula:${model.formula()}")
  }

  test("solve color mapping with arrays and quantifiers") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Define Color datatype
    val redConstr = Core.Constructor("Red", List())
    val greenConstr = Core.Constructor("Green", List())
    val blueConstr = Core.Constructor("Blue", List())
    val colorSort = Core.DatatypeConstructorSort("Color", List(redConstr, greenConstr, blueConstr))
    typeEnv.add("Color", colorSort)

    // Create array mapping boolean pairs to colors
    val colorMap = Core.mkVar("colorMap",
      Core.ArraySort(Core.BoolSort(),
        Core.ArraySort(Core.BoolSort(), colorSort)))

    interpEnv.add("colorMap", colorMap)

    // Create variables for adjacent positions
    val pos1 = Core.mkVar("pos1", Core.BoolSort())
    val pos2 = Core.mkVar("pos2", Core.BoolSort())

    interpEnv.add("pos1", pos1)
    interpEnv.add("pos2", pos2)

    // Add constraint that adjacent positions must have different colors
    val diffColors = Core.mkForall(
      List(("pos1", Core.BoolSort()), ("pos2", Core.BoolSort())),
      Core.mkImplies(
        Core.mkNot(Core.mkEq(pos1, pos2)),
        Core.mkNot(Core.mkEq(
          Core.mkSelect(Core.mkSelect(colorMap, pos1), Core.mkTrue),
          Core.mkSelect(Core.mkSelect(colorMap, pos2), Core.mkTrue)
        ))
      )
    )

    solver.add(List(diffColors))
    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model: ${model.toString}")
    println(s"model.formula:${model.formula()}")
  }

  test("test push pop behavior") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Create variables
    val x = Core.mkVar("x", Core.NumericSort())
    interpEnv.add("x", x)

    // Add initial constraint: x > 0
    solver.add(List(Core.mkGt(x, Core.mkConst(0))))
    assert(solver.checkSat() == Result.SAT, "Initial constraint should be SAT")

    // Push state and add contradicting constraint
    solver.push()
    solver.add(List(Core.mkLt(x, Core.mkConst(0))))
    assert(solver.checkSat() == Result.UNSAT, "Contradicting constraints should be UNSAT")

    // Pop state to remove contradicting constraint
    solver.pop()
    assert(solver.checkSat() == Result.SAT, "After pop, constraints should be SAT again")

    // Verify model
    val model = solver.getModel.get
    val xVal = model.evaluate(x)
    println(s"x value: $xVal")
  }

  test("solve function definition with macro") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Define function f(x) = x + 2 using macro
    val funSort = Core.funSort(List(Core.NumericSort()), Core.NumericSort())

    val mac = Core.mkMacro("f", List(("x", Core.NumericSort())),
      Core.mkAdd(List(Core.mkVar("x", Core.NumericSort()), Core.mkConst(2))))
    val f = solver.defineVar("f", funSort, mac)

    // Assert f(16) = 18
    solver.add(List(
      Core.mkEq(
        Core.mkSubst("app", List(("x", Core.mkConst(16))), mac),
        Core.mkConst(18)
      )
    ))

    // Add y variable and constraint y = f(x) + 3
    val y = Core.mkVar("y", Core.NumericSort())
    interpEnv.add("y", y)
    solver.add(List(
      Core.mkExists(List(("x", Core.NumericSort())),
        Core.mkEq(
          y,
          Core.mkAdd(List(
            Core.mkSubst("app", List(("x", Core.mkVar("x", Core.NumericSort()))), mac),
            Core.mkConst(3)
          ))
        ))
    ))

    val z = Core.mkVar("z", Core.NumericSort())
    interpEnv.add("z", z)
    solver.add(List(Core.mkEq(z, Core.mkSubst("app", List(("x", y)), mac))))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model: ${model.toString}")

    assert(model.evaluate(z) == (model.evaluate(Core.mkAdd(List(y, Core.mkConst(2))))))

    println(s"model.formula: ${model.formula()}")
  }

  test("parsing of SMTInterpol sorts") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)
    val smtSolver = solver.getSolver

    val intSort = solver.lowerSort(Core.numericSort)
    val boolSort = solver.lowerSort(Core.boolSort)
    val arraySort = solver.lowerSort(Core.arraySort(Core.numericSort, Core.boolSort))

    assert(intSort.getName == "Int")
    assert(boolSort.getName == "Bool")
    assert(arraySort.isArraySort)
  }

  test("parsing back SMTInterpol expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)
    val smtSolver = solver.getSolver

    val tt = smtSolver.term("true")
    val ff = smtSolver.term("false")
    assert(solver.liftTerm(tt) == Core.mkTrue)
    assert(solver.liftTerm(ff) == Core.mkFalse)

    val number = smtSolver.numeral("30")
    assert(solver.liftTerm(number) == Core.mkConst(30))
    val plus2 = smtSolver.term("+", number, smtSolver.numeral("32"))
    assert(solver.liftTerm(plus2) == Core.mkAdd(List(Core.mkConst(30), Core.mkConst(32))))

    val var_x = Core.mkVar("x", Core.BoolSort())
    val var_y = Core.mkVar("y", Core.BoolSort())

    interpEnv.add("x", var_x)
    interpEnv.add("y", var_y)

    assert(solver.liftTerm(solver.lower(var_x)) == var_x)

    val b0 = Core.mkImplies(Core.mkOr(List(var_x, var_y)), Core.mkAnd(List(Core.mkNot(var_x), Core.mkFalse)))
    assert(solver.liftTerm(solver.lower(b0)) == b0)

    val boolAnd = Core.mkAnd(List(var_x, var_y))
    val boolOr = Core.mkOr(List(var_x, var_y))
    val boolEq = Core.mkEq(var_x, var_y)
    assert(solver.liftTerm(solver.lower(boolAnd)) == boolAnd)
    assert(solver.liftTerm(solver.lower(boolOr)) == boolOr)
    assert(solver.liftTerm(solver.lower(boolEq)) == boolEq)
  }

  test("parsing back array SMTInterpol expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val arrayVar = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val idx = Core.mkVar("i", Core.NumericSort())
    interpEnv.add("arr", arrayVar)
    interpEnv.add("i", idx)
    val stored = Core.mkStore(arrayVar, idx, Core.mkConst(99))
    val selected = Core.mkSelect(stored, idx)

    val storedTerm = solver.lower(stored)
    val selectedTerm = solver.lower(selected)

    assert(solver.liftTerm(storedTerm) == stored)
    assert(solver.liftTerm(selectedTerm) == selected)
  }

  test("parsing back array SMTInterpol expressions 2") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val arrayVar = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val idx = Core.mkVar("i", Core.NumericSort())
    interpEnv.add("arr", arrayVar)
    interpEnv.add("i", idx)
    val stored = Core.mkStore(arrayVar, idx, Core.mkConst(99))
    val stored2 = Core.mkStore(arrayVar, Core.mkAdd(List(idx, Core.mkConst(1))), Core.mkConst(100))
    val selected = Core.mkSelect(stored, idx)
    val selected2 = Core.mkSelect(arrayVar, selected)
    val storedTerm = solver.lower(stored)
    val selectedTerm = solver.lower(selected)

    assert(solver.liftTerm(solver.lower(stored2)) == stored2)
    assert(solver.liftTerm(solver.lower(selected2)) == selected2)
  }

  test("SMTInterpol forall / exists test") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val forallExpr = Core.mkForall(
      List(("n", Core.NumericSort())),
      Core.mkEq(Core.mkVar("n", Core.NumericSort()), Core.mkVar("n", Core.NumericSort()))
    )

    val nested =
      Core.mkForall(
        List(("m", Core.NumericSort()), ("n", Core.NumericSort()), ("p", Core.boolSort)),
        Core.mkAnd(List(
        Core.mkExists(
          List(("x", Core.numericSort), ("y", Core.boolSort)),
          Core.mkForall(
            List(("a", Core.boolSort), ("b", Core.boolSort)),
            Core.mkAnd(List(
              Core.mkEq(Core.mkVar("a", Core.boolSort), Core.mkConst(true)),
              Core.mkEq(Core.mkVar("b", Core.boolSort), Core.mkConst(true)),
              Core.mkEq(Core.mkVar("x", Core.numericSort), Core.mkConst(1)),
              Core.mkEq(Core.mkVar("y", Core.boolSort), Core.mkConst(true)),
              Core.mkEq(Core.mkVar("m", Core.NumericSort()), Core.mkConst(1)),
              Core.mkEq(Core.mkVar("n", Core.NumericSort()), Core.mkConst(2)),
              Core.mkEq(Core.mkVar("p", Core.boolSort), Core.mkConst(true))
            ))
          )
        ),
          Core.mkForall(List(("o", Core.numericSort)),
            Core.mkEq(Core.mkVar("o", Core.numericSort), Core.mkVar("m", Core.numericSort))
          )
        ))
      )

    val smtForall = solver.lower(forallExpr)
    println(s"SMTInterpol forall: ${smtForall}")

    val smtNested = solver.lower(nested)
    println(s"SMTInterpol nested forall: ${smtNested}")
  }

  test("parsing back complex SMTInterpol expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val forallExpr = Core.mkForall(
      List(("n", Core.NumericSort())),
      Core.mkEq(Core.mkVar("n", Core.NumericSort()), Core.mkVar("n", Core.NumericSort()))
    )
    val existsExpr = Core.mkExists(
      List(("b", Core.BoolSort())),
      Core.mkVar("b", Core.BoolSort())
    )

    val forallTerm = solver.lower(forallExpr)
    val existsTerm = solver.lower(existsExpr)

    assert(solver.liftTerm(forallTerm) == forallExpr)
    assert(solver.liftTerm(existsTerm) == existsExpr)
  }

  test("parsing back ADT SMTInterpol expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)
    val smtSolver = solver.getSolver

    val pointConstructor = Core.constructor("Point", List(
      ("x", Core.numericSort),
      ("y", Core.numericSort)
    ))
    val pointSortBox = Core.datatypeSort("Point", List(pointConstructor))
    typeEnv.add("Point", pointSortBox)
    val pointSort = pointSortBox.sort

    // Lower the sort to ensure it's declared in SMTInterpol
    val smtPointSort = solver.defineSort(pointSort)

    println(s"SMTInterpol Point sort: ${smtPointSort}")
    assert(smtPointSort.getName == "Point")
  }

  /* ***** TODO ***
  test("alias sort lowering and evaluation") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val base = Core.UnInterpretedSort("Base", 0)
    typeEnv.add("Base", base.box)

    val alias = Core.AliasSort("AliasBase", Nil, base)
    typeEnv.add("AliasBase", alias.box)

    val x = Core.mkVar("x", alias)
    interpEnv.add("x", x)

    solver.add(List(Core.mkEq(x, Core.mkConst(Core.SortValue.UnInterpretedValue("c0", alias)))))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    val value = model.evaluate(x)
    assert(value.toString.contains("c0"))
  }*/

  test("model asTerm and blocking clauses") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val x = Core.mkVar("x", Core.BoolSort())
    interpEnv.add("x", x)

    assert(solver.checkSat() == Result.SAT)
    val model1 = solver.getModel.get
    val firstValue = model1.evaluate(x).toString

    solver.addTerms(List(model1.asNegatedTerm()))
    assert(solver.checkSat() == Result.SAT)
    val model2 = solver.getModel.get
    val secondValue = model2.evaluate(x).toString
    assert(firstValue != secondValue)

    solver.addTerms(List(model2.asTerm()))
    assert(solver.checkSat() == Result.SAT)
    solver.addTerms(List(model2.asNegatedTerm()))
    assert(solver.checkSat() == Result.UNSAT)
  }

  test("allSat with boolean variables only") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Create two boolean variables
    val x = Core.mkVar("x", Core.BoolSort())
    val y = Core.mkVar("y", Core.BoolSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)

    // Add constraint: x OR y (should have 3 satisfying models: TT, TF, FT)
    solver.add(List(Core.mkOr(List(x, y))))

    // Get all satisfying models


    val models = solver.allSat(Set(("x", Core.boolSort), ("y", Core.boolSort)))

    // Should have exactly 3 models
    assert(models.length == 3, s"Expected 3 models, got ${models.length}")

    // Each model should satisfy the constraint
    models.foreach { model =>
      val xVal = model.evaluate(x)
      val yVal = model.evaluate(y)
      println(s"Model: x=${xVal}, y=${yVal}")
      // At least one should be true
      assert(xVal.toString.contains("true") || yVal.toString.contains("true"))
    }
  }

  test("allSat with finite universe sorts and arrays") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Create a finite universe sort with 2 elements
    val colorSort = Core.FiniteUniverseSort("Color", 2)
    typeEnv.add("Color", colorSort)

    // Create an array mapping from Color to Bool
    val arr = Core.mkVar("arr", Core.ArraySort(colorSort, Core.BoolSort()))
    interpEnv.add("arr", arr)

    // Create variable of Color sort
    val c = Core.mkVar("c", colorSort)
    interpEnv.add("c", c)

    // Constraint: arr[c] = true
    // This should have 2^2 = 4 models (2 choices for c, 2 independent choices for the other color's value)
    solver.add(List(Core.mkSelect(arr, c)))

    // Get all satisfying models
    val models = solver.allSat(Set(("arr", Core.arraySort(colorSort, Core.boolSort)), ("c", colorSort)))

    println(s"Found ${models.length} models")
    models.foreach { model =>
      println(s"Model: ${model.formula()}")
    }

    // Should have exactly 4 models
    assert(models.length == 4, s"Expected 4 models, got ${models.length}")
  }

  test("allSat with multiple finite universe variables") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    // Create a finite universe sort with 3 elements
    val signalSort = Core.FiniteUniverseSort("Signal", 3)
    typeEnv.add("Signal", signalSort)

    // Create two variables of Signal sort
    val s1 = Core.mkVar("s1", signalSort)
    val s2 = Core.mkVar("s2", signalSort)

    interpEnv.add("s1", s1)
    interpEnv.add("s2", s2)

    // Constraint: s1 != s2 (should have 3*2 = 6 models)
    solver.add(List(Core.mkNot(Core.mkEq(s1, s2))))

    // Get all satisfying models
    val models = solver.allSat(Set(("s1", signalSort), ("s2", signalSort)))

    println(s"Found ${models.length} models for s1 != s2")
    models.foreach { model =>
      val s1Val = model.evaluate(s1)
      val s2Val = model.evaluate(s2)
      println(s"Model: s1=${s1Val}, s2=${s2Val}")
    }

    // Should have exactly 6 models (3 choices for s1, 2 remaining choices for s2)
    assert(models.length == 6, s"Expected 6 models, got ${models.length}")
  }

}
