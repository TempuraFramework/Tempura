package org.abstractpredicates.smt

import com.microsoft.z3
import com.microsoft.z3.enumerations.Z3_decl_kind
import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.expression.Syntax.*

class Z3BackendTests extends AnyFunSuite {


  test("solve boolean formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
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
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
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


  test("solve boolean-indexed and nested arrays") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    // Define nested array types for 2D array simulation: bool->(bool->int)
    val arr1 = Core.mkVar("arr1", Core.ArraySort(Core.BoolSort(), Core.NumericSort()))
    val arr2 = Core.mkVar("arr2", Core.ArraySort(Core.BoolSort(), Core.ArraySort(Core.BoolSort(), Core.NumericSort())))

    // Define index variables
    val b1 = Core.mkVar("b1", Core.BoolSort())
    val b2 = Core.mkVar("b2", Core.BoolSort())
    val v1 = Core.mkVar("v1", Core.NumericSort())
    val v2 = Core.mkVar("v2", Core.NumericSort())

    interpEnv.add("arr1", arr1)
    interpEnv.add("arr2", arr2)
    interpEnv.add("b1", b1)
    interpEnv.add("b2", b2)
    interpEnv.add("v1", v1)
    interpEnv.add("v2", v2)
    
    solver.add(List(
      Core.mkEq(Core.mkSelect(arr1, b1), v1),
      Core.mkEq(Core.mkSelect(Core.mkSelect(arr2, b1), b2), v2),
      Core.mkEq(b1, Core.mkTrue),
      Core.mkEq(b2, Core.mkFalse),
      Core.mkEq(v1, Core.mkConst(10)),
      Core.mkEq(v2, Core.mkConst(20))
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model.formula:${model.formula()}")
    println(s"model value of b1 = ${model.evaluate(b1)}")
    println(s"model value of b2 = ${model.evaluate(b2)}")
    println(s"model value of v1 = ${model.evaluate(v1)}")
    println(s"model value of v2 = ${model.evaluate(v2)}")
    // Strict assertions
    //assert(model.formula().contains("b1 = true"))
    //assert(model.formula().contains("b2 = false"))
    //assert(model.formula().contains("v1 = 10"))
    //assert(model.formula().contains("v2 = 20"))
  }

  test("solve array with universal quantifier") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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
  /*
  test("solve binary tree datatype with quantifiers") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    // Define binary tree datatype
    val treeSort = Core.DatatypeConstructorSort("treeSort", List())

    val leafConstructor = Core.Constructor("Leaf", List(("value", Core.NumericSort())))
    val nodeConstructor = Core.Constructor("Node", List(("left", treeSort), ("right", treeSort)))

    typeEnv.add("Tree", treeSort)

    // Declare variables
    val tree = Core.mkVar("tree", treeSort)
    val x = Core.mkVar("x", Core.NumericSort())

    interpEnv.add("tree", tree)
    interpEnv.add("x", x)

    checked(solver.declareVar("tree", treeSort))
    checked(solver.declareVar("x", Core.NumericSort()))

    // Create a constraint that all values in the tree are positive
    val isPositive = Core.mkForall(
      List(("x", Core.NumericSort())),
      Core.mkImplies(
        Core.mkOr(List(
          Core.mkEq(x, Core.mkSelect(tree, Core.mkConst("value"))),
          Core.mkEq(x, Core.mkSelect(Core.mkSelect(tree, Core.mkConst("left")), Core.mkConst("value"))),
          Core.mkEq(x, Core.mkSelect(Core.mkSelect(tree, Core.mkConst("right")), Core.mkConst("value")))
        )),
        Core.mkGt(x, Core.mkConst(0))
      )
    )

    solver.add(List(isPositive))
    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model.formula:${model.formula()}")

    // Verify that the model satisfies our constraints
    val treeValue = model.evaluate(Core.mkSelect(tree, Core.mkConst("value")))
    assert(treeValue.toInt > 0, "Root value should be positive")
  }
  */

  test("solve color mapping with arrays and quantifiers") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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
    //assert(, s"x value should be positive, got $xVal")
    println(s"x value: $xVal")
  }

  test("solve function definition with macro") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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

    //print(solver.getHistory.mkString("\n"))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    println(s"model: ${model.toString}")

    assert(model.evaluate(z) == (model.evaluate(Core.mkAdd(List(y, Core.mkConst(2))))))

    println(s"model.formula: ${model.formula()}")
  }

  test("parsing of Z3 sorts") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    assert(solver.lowerSort(Core.numericSort) == ctx.getIntSort)
    assert(solver.lowerSort(Core.boolSort) == ctx.getBoolSort)
    assert(solver.lowerSort(Core.arraySort(Core.numericSort, Core.boolSort)) == ctx.mkArraySort(ctx.getIntSort, ctx.getBoolSort))
  }

  test("parsing back Z3 expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    
    println(s"z3 solver version: ${solver.getVersion}")
    
    val ctx = solver.getContext

    val tt = ctx.mkTrue()
    val ff = ctx.mkFalse()
    assert(solver.liftTerm(tt.asInstanceOf[solver.LoweredTerm]) == Core.mkTrue)
    assert(solver.liftTerm(ff.asInstanceOf[solver.LoweredTerm]) == Core.mkFalse)

    val number = ctx.mkNumeral(30, ctx.getIntSort)
    assert(solver.liftTerm(number.asInstanceOf[solver.LoweredTerm]) == Core.mkConst(30))
    val plus2 = ctx.mkAdd(number, ctx.mkNumeral(32, ctx.getIntSort))
    assert(solver.liftTerm(plus2.asInstanceOf[solver.LoweredTerm]) == Core.mkAdd(List(Core.mkConst(30), Core.mkConst(32))))


    val p = ctx.mkFuncDecl("p", Array[z3.Sort](), ctx.getBoolSort)
    assert(p.getDeclKind != Z3_decl_kind.Z3_OP_RECURSIVE)
    assert(p.getDeclKind == Z3_decl_kind.Z3_OP_UNINTERPRETED)
    val liftedP = solver.liftTerm(p.apply().asInstanceOf[solver.LoweredTerm])
    assert(liftedP == Core.mkVar("p", Core.BoolSort()))


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

  test("parsing back array Z3 expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    val arrayVar = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val idx = Core.mkVar("i", Core.NumericSort())
    interpEnv.add("arr", arrayVar)
    interpEnv.add("i", idx)
    val stored = Core.mkStore(arrayVar, idx, Core.mkConst(99))
    val selected = Core.mkSelect(stored, idx)

    val storedZ3 = solver.lower(stored)
    val selectedZ3 = solver.lower(selected)

    assert(solver.liftTerm(storedZ3) == stored)
    assert(solver.liftTerm(selectedZ3) == selected)
  }


  test("parsing back array Z3 expressions 2") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    val arrayVar = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    val idx = Core.mkVar("i", Core.NumericSort())
    interpEnv.add("arr", arrayVar)
    interpEnv.add("i", idx)
    val stored = Core.mkStore(arrayVar, idx, Core.mkConst(99))
    val stored2 = Core.mkStore(arrayVar, Core.mkAdd(List(idx, Core.mkConst(1))), Core.mkConst(100))
    val selected = Core.mkSelect(stored, idx)
    val selected2 = Core.mkSelect(arrayVar, selected)
    val storedZ3 = solver.lower(stored)
    val selectedZ3 = solver.lower(selected)

    assert(solver.liftTerm(solver.lower(stored2)) == stored2)
    assert(solver.liftTerm(solver.lower(selected2)) == selected2)
  }

  test("z3 forall / exists test") {

    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

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


    val z3Forall = solver.lower(forallExpr).asInstanceOf[z3.Quantifier]
    val z3ForallVar = z3Forall.getBoundVariableNames
    val z3ForallBody = z3Forall.getBody

    println(s"z3 forall: ${z3Forall}")
    println(s"z3 forall var: ${z3ForallVar(0).toString}")
    println(s"z3 forall body: ${z3ForallBody}")

    println("---------------------------------------")


    val z3Nested = solver.lower(nested).asInstanceOf[z3.Quantifier]
    val z3NestedVars = z3Nested.getBoundVariableNames.toList.map(x => x.toString)
    val z3NestedBody = z3Nested.getBody

    val z3Nested1 = z3Nested.getBody.getArgs()(0).asInstanceOf[z3.Quantifier]
    val z3Nested1Vars = z3Nested1.getBoundVariableNames.toList.map(x => x.toString)
    val z3Nested1Body = z3Nested.getBody

    val z3Nested2 = z3Nested1.getBody.asInstanceOf[z3.Quantifier]
    val z3Nested2Vars = z3Nested2.getBoundVariableNames.toList.map(x => x.toString)
    val z3Nested2Body = z3Nested2.getBody

    println(s" *** Toplevel number of bound vars: ${z3Nested.getNumBound}")
    println(s" *** Middle number of bound vars: ${z3Nested1.getNumBound}")
    println(s" *** Bottomlevel number of bound vars: ${z3Nested2.getNumBound}")

    println(s"z3 nested forall: ${z3Nested}")
    println(s"z3 nested forall var: ${z3NestedVars}")
    println(s"z3 nested forall body: ${z3NestedBody}")

    println(s"z3 nested forall-exists: ${z3Nested1}")
    println(s"z3 nested forall-exists var: ${z3Nested1Vars}")
    println(s"z3 nested forall-exists body: ${z3Nested1Body}")

    println(s"z3 nested forall-exists-forall: ${z3Nested2}")
    println(s"z3 nested forall-exists-forall var: ${z3Nested2Vars}")
    println(s"z3 nested forall-exists-forall body: ${z3Nested2Body}")


    println("----------")
    println(s"other case: ${z3Nested.getBody.getArgs()(1).asInstanceOf[z3.Quantifier]}")
    println(s"other case var: ${z3Nested.getBody.getArgs()(1).asInstanceOf[z3.Quantifier].getBoundVariableNames.toList}")
    println(s"other case body: ${z3Nested.getBody.getArgs()(1).asInstanceOf[z3.Quantifier].getBody}")
    println("----------")

  }

  test("parsing back complex Z3 expressions") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

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

  test("parsing back ADT Z3 expressions") { // TODO BUG
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    val pointConstructor = Core.constructor("Point", List(
      ("x", Core.numericSort),
      ("y", Core.numericSort)
    ))
    val pointSortBox = Core.datatypeSort("Point", List(pointConstructor))
    typeEnv.add("Point", pointSortBox)
    val pointSort = pointSortBox.sort
    val z3PointSort = solver.defineSort(pointSort).asInstanceOf[z3.DatatypeSort[z3.Sort]]
    val pointCtorDecl = z3PointSort.getConstructors()(0)
    val pointValue = pointCtorDecl.apply(ctx.mkInt(1), ctx.mkInt(2))
    val xAccessor = z3PointSort.getAccessors()(0)(0)
    val liftedAccessor = solver.liftTerm(xAccessor.apply(pointValue).asInstanceOf[solver.LoweredTerm])
    val expectedPoint = Core.mkDatatypeAccessor(
      pointSort,
      Core.instantiatedConstructor(
        pointConstructor,
        List(Core.mkConst(1).box(), Core.mkConst(2).box())
      )
    )
    assert(liftedAccessor == expectedPoint)
  }


  test("allSat with boolean variables only") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

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

  test("cardinality constraints via at-most/at-least") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    val a = Core.mkVar("a", Core.BoolSort())
    val b = Core.mkVar("b", Core.BoolSort())
    val c = Core.mkVar("c", Core.BoolSort())

    interpEnv.add("a", a)
    interpEnv.add("b", b)
    interpEnv.add("c", c)

    val vars = List(a.asInstanceOf[Core.Var[Core.BoolSort]],
      b.asInstanceOf[Core.Var[Core.BoolSort]],
      c.asInstanceOf[Core.Var[Core.BoolSort]])

    // Exactly one variable should be true
    val atMostOne = Core.mkAtMost(1, vars)
    val atLeastOne = Core.mkAtLeast(1, vars)

    solver.add(List(
      atMostOne,
      atLeastOne,
      Core.mkEq(a, Core.mkTrue),
      Core.mkEq(b, Core.mkFalse)
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    val aVal = model.evaluate(a).toString
    val bVal = model.evaluate(b).toString
    val cVal = model.evaluate(c).toString
    assert(aVal.contains("true"))
    assert(bVal.contains("false"))
    assert(cVal.contains("false"))
  }

  test("lowering of ite Top node") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    val flag = Core.mkVar("flag", Core.BoolSort())
    val iteExpr = Core.mkTop("=>", flag, Core.mkConst(7), Core.mkConst(3), Core.NumericSort())
    val result = Core.mkVar("res", Core.NumericSort())

    interpEnv.add("flag", flag)
    interpEnv.add("res", result)

    solver.add(List(
      Core.mkEq(flag, Core.mkTrue),
      Core.mkEq(result, iteExpr)
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    val resValue = model.evaluate(result)
    assert(resValue.toString.contains("7"))
  }

  test("division lowering") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    val quotient = Core.mkVar("q", Core.NumericSort())
    interpEnv.add("q", quotient)

    val division = Core.mkBop("/", Core.mkConst(10), Core.mkConst(2), Core.NumericSort())

    solver.add(List(
      Core.mkEq(quotient, division)
    ))

    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    assert(model.evaluate(quotient).toString.contains("5"))
  }

  test("datatype constructor and recognizer lifting") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    val pointConstructor = Core.constructor("Point", List(
      ("x", Core.numericSort),
      ("y", Core.numericSort)
    ))
    val pointSortBox = Core.datatypeSort("Point", List(pointConstructor))
    typeEnv.add("Point", pointSortBox)
    val pointSort = pointSortBox.sort
    val z3PointSort = solver.defineSort(pointSort).asInstanceOf[z3.DatatypeSort[z3.Sort]]
    val pointCtorDecl = z3PointSort.getConstructors()(0)
    val pointValue = pointCtorDecl.apply(ctx.mkInt(4), ctx.mkInt(9))

    val expectedPoint = Core.mkDatatypeAccessor(
      pointSort,
      Core.instantiatedConstructor(
        pointConstructor,
        List(Core.mkConst(4).box(), Core.mkConst(9).box())
      )
    )

    assert(solver.liftTerm(pointValue.asInstanceOf[solver.LoweredTerm]) == expectedPoint)

    val recognizer = z3PointSort.getRecognizers()(0)
    val liftedRecognizer = solver.liftTerm(recognizer.apply(pointValue).asInstanceOf[solver.LoweredTerm])
    val expectedRecognizer = Core.mkDatatypeRecognizer(pointSort, "Point", expectedPoint)
    assert(liftedRecognizer == expectedRecognizer)
  }

  test("parsing of finite sort elements") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val ctx = solver.getContext

    val fSort = typeEnv |- Core.finiteSort("U", 3)
    val fVar1 = interpEnv |- ("var1", fSort)
    val fVar2 = interpEnv |- ("var2", fSort)

    solver.add(List(Core.mkNot(Core.mkEq(fVar1, fVar2))))
    assert(solver.checkSat() == Result.SAT)
    val model = solver.getModel.get
    val formula = model.formula()
    println(s"formula: ${formula}")
  }

  test("model blocking with asTerm and asNegatedTerm") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.BoolSort())
    interpEnv.add("x", x)

    solver.add(List()) // no constraints, two models exist
    assert(solver.checkSat() == Result.SAT)
    val model1 = solver.getModel.get
    val value1 = model1.evaluate(x).toString

    // Block current model
    solver.addTerms(List(model1.asNegatedTerm()))
    assert(solver.checkSat() == Result.SAT)
    val model2 = solver.getModel.get
    val value2 = model2.evaluate(x).toString
    assert(value1 != value2, "Blocking clause should exclude previous model")

    // Constrain solver to the second model only and ensure unsat afterwards
    solver.addTerms(List(model2.asTerm()))
    assert(solver.checkSat() == Result.SAT)
    solver.addTerms(List(model2.asNegatedTerm()))
    assert(solver.checkSat() == Result.UNSAT)
  }
}
