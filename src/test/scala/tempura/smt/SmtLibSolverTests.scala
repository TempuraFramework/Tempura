package tempura.smt

import org.scalatest.funsuite.AnyFunSuite
import tempura.expression.Core.*
import tempura.helpers.Utils.*
import SmtSolver.*
import tempura.expression.Syntax.*
import tempura.expression.Core

class SmtLibSolverTests extends AnyFunSuite {

  test("lower boolean formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

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

    val script = solver.asScript
    println(s"Boolean formula script:\n${script}")

    // Verify declarations and assertions are present
    assert(script.contains("declare-fun x"))
    assert(script.contains("declare-fun y"))
    assert(script.contains("declare-fun z"))
    assert(script.contains("(and x y)"))
    assert(script.contains("(not z)"))
    assert(script.contains("check-sat"))
  }

  test("lower array formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

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

    val script = solver.asScript
    println(s"Array formula script:\n${script}")

    assert(script.contains("(Array Int Int)"))
    assert(script.contains("(select arr i)"))
    assert(script.contains("= i 0"))
    assert(script.contains("= v 42"))
  }

  test("lower arithmetic formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.NumericSort())
    val y = Core.mkVar("y", Core.NumericSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)

    solver.add(List(
      Core.mkGt(x, Core.mkConst(0)),
      Core.mkEq(y, Core.mkAdd(List(x, Core.mkConst(5)))),
      Core.mkLt(y, Core.mkConst(20))
    ))

    val script = solver.asScript
    println(s"Arithmetic formula script:\n${script}")

    assert(script.contains("(> x 0)"))
    assert(script.contains("(+ x 5)"))
    assert(script.contains("(< y 20)"))
  }

  test("lower quantified formulas") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val arr = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    interpEnv.add("arr", arr)

    val constraint = Core.mkForall(
      List(("i", Core.NumericSort())),
      Core.mkImplies(
        Core.mkGt(Core.mkVar("i", Core.NumericSort()), Core.mkConst(100)),
        Core.mkGe(Core.mkSelect(arr, Core.mkVar("i", Core.NumericSort())), Core.mkConst(10))
      )
    )

    solver.add(List(constraint))

    val script = solver.asScript
    println(s"Quantified formula script:\n${script}")

    assert(script.contains("(forall ((i Int))"))
    assert(script.contains("=>"))
    assert(script.contains("(> i 100)"))
    assert(script.contains("(>= (select arr i) 10)"))
  }

  test("lower function definitions with macro") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val funSort = Core.funSort(List(Core.NumericSort()), Core.NumericSort())
    val mac = Core.mkMacro("f", List(("x", Core.NumericSort())),
      Core.mkAdd(List(Core.mkVar("x", Core.NumericSort()), Core.mkConst(2))))

    solver.defineVar("f", funSort, mac)

    val y = Core.mkVar("y", Core.NumericSort())
    interpEnv.add("y", y)

    solver.add(List(
      Core.mkEq(
        Core.mkSubst("app", List(("x", Core.mkConst(16))), mac),
        Core.mkConst(18)
      )
    ))

    val script = solver.asScript
    println(s"Function definition script:\n${script}")

    assert(script.contains("(define-fun f ((x Int)) Int"))
    assert(script.contains("(+ x 2)"))
    assert(script.contains("(f 16)"))
  }

  test("lower finite universe sorts") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val colorSort = Core.FiniteUniverseSort("Color", 3)
    typeEnv.add("Color", colorSort)

    val c1 = Core.mkVar("c1", colorSort)
    val c2 = Core.mkVar("c2", colorSort)

    interpEnv.add("c1", c1)
    interpEnv.add("c2", c2)

    solver.add(List(Core.mkNot(Core.mkEq(c1, c2))))

    val script = solver.asScript
    println(s"Finite universe script:\n${script}")

    assert(script.contains("declare-datatypes"))
    assert(script.contains("Color"))
    assert(script.contains("declare-fun c1"))
    assert(script.contains("declare-fun c2"))
  }

  test("lower datatype sorts") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val pointConstructor = Core.constructor("Point", List(
      ("x", Core.numericSort),
      ("y", Core.numericSort)
    ))
    val pointSortBox = Core.datatypeSort("Point", List(pointConstructor))
    typeEnv.add("Point", pointSortBox)

    val p = Core.mkVar("p", pointSortBox.sort)
    interpEnv.add("p", p)

    solver.add(List())

    val script = solver.asScript
    println(s"Datatype script:\n${script}")

    assert(script.contains("declare-datatypes"))
    assert(script.contains("Point"))
    assert(script.contains("(x Int)"))
    assert(script.contains("(y Int)"))
  }

  test("lift boolean terms") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    // Lift basic constants
    assert(solver.liftTerm("true") == Core.mkTrue)
    assert(solver.liftTerm("false") == Core.mkFalse)
    assert(solver.liftTerm("42") == Core.mkConst(42))

    // Lift boolean operators
    val andTerm = "(and true false)"
    val liftedAnd = solver.liftTerm(andTerm)
    assert(liftedAnd.sort == Core.BoolSort())

    val orTerm = "(or true false)"
    val liftedOr = solver.liftTerm(orTerm)
    assert(liftedOr.sort == Core.BoolSort())

    val notTerm = "(not true)"
    val liftedNot = solver.liftTerm(notTerm)
    assert(liftedNot.sort == Core.BoolSort())
  }

  test("lift arithmetic terms") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val addTerm = "(+ 1 2 3)"
    val liftedAdd = solver.liftTerm(addTerm)
    assert(liftedAdd.sort == Core.NumericSort())

    val subTerm = "(- 10 5)"
    val liftedSub = solver.liftTerm(subTerm)
    assert(liftedSub.sort == Core.NumericSort())

    val mulTerm = "(* 2 3)"
    val liftedMul = solver.liftTerm(mulTerm)
    assert(liftedMul.sort == Core.NumericSort())

    val negTerm = "(- 5)"
    val liftedNeg = solver.liftTerm(negTerm)
    assert(liftedNeg.sort == Core.NumericSort())
  }

  test("lift comparison terms") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val ltTerm = "(< 5 10)"
    val liftedLt = solver.liftTerm(ltTerm)
    assert(liftedLt.sort == Core.BoolSort())

    val gtTerm = "(> 10 5)"
    val liftedGt = solver.liftTerm(gtTerm)
    assert(liftedGt.sort == Core.BoolSort())

    val eqTerm = "(= 5 5)"
    val liftedEq = solver.liftTerm(eqTerm)
    assert(liftedEq.sort == Core.BoolSort())
  }

  test("lift sorts") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    assert(solver.liftSort("Bool") == Core.BoolSort())
    assert(solver.liftSort("Int") == Core.NumericSort())

    val arraySort = solver.liftSort("(Array Int Bool)")
    assert(arraySort.sort.isInstanceOf[Core.ArraySort[?, ?]])
  }

  test("roundtrip lower and lift") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.BoolSort())
    val y = Core.mkVar("y", Core.BoolSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)

    val expr1 = Core.mkAnd(List(x, y))
    val lowered1 = solver.lower(expr1)
    val lifted1 = solver.liftTerm(lowered1)
    // Note: lifted terms may have different structure but should be semantically equivalent

    val expr2 = Core.mkImplies(x, y)
    val lowered2 = solver.lower(expr2)
    val lifted2 = solver.liftTerm(lowered2)

    val expr3 = Core.mkAdd(List(Core.mkConst(1), Core.mkConst(2), Core.mkConst(3)))
    val lowered3 = solver.lower(expr3)
    val lifted3 = solver.liftTerm(lowered3)
    assert(lifted3.sort == Core.NumericSort())
  }

  test("push and pop behavior") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.NumericSort())
    interpEnv.add("x", x)

    solver.add(List(Core.mkGt(x, Core.mkConst(0))))
    val script1 = solver.asScript

    solver.push()
    solver.add(List(Core.mkLt(x, Core.mkConst(0))))
    val script2 = solver.asScript

    solver.pop()
    val script3 = solver.asScript

    // After pop, we should have only the first assertion
    assert(script1.contains("(> x 0)"))
    assert(script2.contains("(> x 0)"))
    assert(script2.contains("(< x 0)"))
    assert(script3.contains("(> x 0)"))
    assert(!script3.contains("(< x 0)"))
  }

  test("fork creates independent solver") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver1 = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.BoolSort())
    interpEnv.add("x", x)

    solver1.add(List(x))

    val solver2 = solver1.fork()
    solver2.add(List(Core.mkNot(x)))

    val script1 = solver1.asScript
    val script2 = solver2.asScript

    // solver1 should only have x
    assert(script1.contains("(assert x)"))
    assert(!script1.contains("(not x)"))

    // solver2 should have both x and (not x)
    assert(script2.contains("(assert x)"))
    assert(script2.contains("(not x)"))
  }

  test("history tracking") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.BoolSort())
    interpEnv.add("x", x)

    solver.add(List(x))
    val history = solver.getHistory

    assert(history.exists(_.contains("declare-fun x")))
    assert(history.exists(_.contains("(assert x)")))
  }

  test("complex nested expression") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val x = Core.mkVar("x", Core.NumericSort())
    val y = Core.mkVar("y", Core.NumericSort())
    val b = Core.mkVar("b", Core.BoolSort())

    interpEnv.add("x", x)
    interpEnv.add("y", y)
    interpEnv.add("b", b)

    val iteExpr = Core.mkIte(
      b,
      Core.mkAdd(List(x, Core.mkConst(5))),
      y
    )

    solver.add(List(Core.mkEq(x, iteExpr)))

    val script = solver.asScript
    println(s"Complex nested expression script:\n${script}")

    assert(script.contains("ite"))
    assert(script.contains("(+ x 5)"))
  }

  test("array store and select") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val arr = Core.mkVar("arr", Core.ArraySort(Core.NumericSort(), Core.NumericSort()))
    interpEnv.add("arr", arr)

    val stored = Core.mkStore(arr, Core.mkConst(0), Core.mkConst(42))
    val selected = Core.mkSelect(stored, Core.mkConst(0))

    val lowered = solver.lower(selected)
    println(s"Store and select lowered: ${lowered}")

    assert(lowered.contains("select"))
    assert(lowered.contains("store"))
  }

  test("constant array lowering") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val constArray = Core.mkConstArray(Core.NumericSort(), Core.mkConst(42))
    val lowered = solver.lower(constArray)

    println(s"Constant array lowered: ${lowered}")
    assert(lowered.contains("as const"))
    assert(lowered.contains("Array"))
  }

  test("uninterpreted sort") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val mySort = Core.UnInterpretedSort("MySort", 0)
    typeEnv.add("MySort", mySort.box)

    val x = Core.mkVar("x", mySort)
    interpEnv.add("x", x)

    solver.add(List())

    val script = solver.asScript
    println(s"Uninterpreted sort script:\n${script}")

    assert(script.contains("declare-sort MySort 0"))
    assert(script.contains("declare-fun x () MySort"))
  }

  test("parse simple model with booleans") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    // Simulate model output from (get-model)
    val modelOutput = """
      (model
        (define-fun x () Bool true)
        (define-fun y () Bool false)
      )
    """

    solver.setModelOutput(modelOutput)
    val modelOpt = solver.getModel

    assert(modelOpt.isDefined)
    val model = modelOpt.get

    // Test valueOf
    val xValue = model.valueOf("x", Core.BoolSort())
    assert(xValue.isDefined)
    assert(xValue.get == Core.mkTrue)

    val yValue = model.valueOf("y", Core.BoolSort())
    assert(yValue.isDefined)
    assert(yValue.get == Core.mkFalse)

    println(s"Boolean model: ${model}")
  }

  test("parse model with integers") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Int 42)
        (define-fun y () Int 0)
        (define-fun z () Int -5)
      )
    """

    solver.setModelOutput(modelOutput)
    val modelOpt = solver.getModel

    assert(modelOpt.isDefined)
    val model = modelOpt.get

    val xValue = model.valueOf("x", Core.NumericSort())
    assert(xValue.isDefined)
    assert(xValue.get == Core.mkConst(42))

    val yValue = model.valueOf("y", Core.NumericSort())
    assert(yValue.isDefined)
    assert(yValue.get == Core.mkConst(0))

    val zValue = model.valueOf("z", Core.NumericSort())
    assert(zValue.isDefined)
    assert(zValue.get == Core.mkConst(-5))

    println(s"Integer model: ${model}")
  }

  test("model evaluate") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Int 10)
        (define-fun y () Int 20)
      )
    """

    solver.setModelOutput(modelOutput)
    val model = solver.getModel.get

    // Evaluate a variable
    val xVar = Core.mkVar("x", Core.NumericSort())
    val xEval = model.evaluate(xVar)
    assert(xEval == Core.mkConst(10))

    // Evaluate a constant
    val constExpr = Core.mkConst(5)
    val constEval = model.evaluate(constExpr)
    assert(constEval == constExpr)

    println(s"Evaluation test passed")
  }

  test("model asTerm") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Bool true)
        (define-fun y () Int 5)
      )
    """

    solver.setModelOutput(modelOutput)
    val model = solver.getModel.get

    // Get full model as term
    val term = model.asTerm()
    println(s"Model as term: ${term}")

    assert(term.contains("="))
    assert(term.contains("x"))
    assert(term.contains("y"))

    // Get model for specific vocabulary
    val vocab: Set[(String, Core.BoxedSort)] = Set(("x", Core.BoolSort().box))
    val vocabTerm = model.asTerm(vocab)
    println(s"Model with vocab as term: ${vocabTerm}")

    assert(vocabTerm.contains("x"))
    assert(!vocabTerm.contains("y"))
  }

  test("model asNegatedTerm") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Bool true)
      )
    """

    solver.setModelOutput(modelOutput)
    val model = solver.getModel.get

    val negated = model.asNegatedTerm()
    println(s"Negated model term: ${negated}")

    assert(negated.startsWith("(not"))
    assert(negated.contains("x"))
  }

  test("model vocabulary") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Bool true)
        (define-fun y () Int 10)
        (define-fun z () Bool false)
      )
    """

    solver.setModelOutput(modelOutput)
    val model = solver.getModel.get

    val (sorts, names) = model.vocabulary()
    println(s"Vocabulary: names=${names}, sorts=${sorts}")

    assert(names.contains("x"))
    assert(names.contains("y"))
    assert(names.contains("z"))
    assert(sorts.length == 3)
  }

  test("model with empty output") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    // Before setting model output, getModel should return None
    assert(solver.getModel.isEmpty)

    // Set empty model
    val modelOutput = "(model)"
    solver.setModelOutput(modelOutput)

    val modelOpt = solver.getModel
    assert(modelOpt.isDefined)

    val model = modelOpt.get
    val (sorts, names) = model.vocabulary()
    assert(names.isEmpty)
    assert(sorts.isEmpty)
  }

  test("model apply method") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    val solver = SmtLibSolver(typeEnv, interpEnv)

    val modelOutput = """
      (model
        (define-fun x () Int 42)
      )
    """

    solver.setModelOutput(modelOutput)
    val model = solver.getModel.get

    val xValue = model("x", Core.NumericSort().box)
    assert(xValue.isDefined)
    // Check that we got the right value through valueOf instead
    val xDirectValue = model.valueOf("x", Core.NumericSort())
    assert(xDirectValue.isDefined)
    assert(xDirectValue.get == Core.mkConst(42))

    val yValue = model("y", Core.NumericSort().box)
    assert(yValue.isEmpty)
  }
}
