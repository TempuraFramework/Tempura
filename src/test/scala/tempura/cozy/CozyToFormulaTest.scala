package tempura.cozy

import clojure.lang.{Namespace, Symbol}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAll
import tempura.expression.Core
import tempura.expression.Core.*

class CozyToFormulaTest extends AnyFunSuite with BeforeAndAfterAll {

  private var previousNs: CozyNamespace = _
  private var boolVar: Core.Expr[BoolSort] = _
  private var numVar: Core.Expr[NumericSort] = _
  private var arrVar: Core.Expr[ArraySort[NumericSort, NumericSort]] = _
  private var funVar: Core.Expr[FunSort[NumericSort]] = _
  private var funVarSort: FunSort[NumericSort] = _
  private var doubleMacro: Core.Expr[FunSort[NumericSort]] = _

  override protected def beforeAll(): Unit = {
    super.beforeAll()
    previousNs = CS.currentNS

    val ns = Namespace.findOrCreate(Symbol.intern("tempura.cozy.test"))
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    boolVar = Core.mkVar("b", BoolSort())
    numVar = Core.mkVar("n", NumericSort())
    arrVar = Core.mkVar("arr", ArraySort(NumericSort(), NumericSort()))
    funVarSort = FunSort(List(Core.numericSort), NumericSort())
    funVar = Core.mkVar("f", funVarSort)
    doubleMacro =
      Core.mkMacro(
        "double",
        List(("x", Core.numericSort)),
        Core.mkAdd(List(Core.mkVar("x", NumericSort()), Core.mkVar("x", NumericSort())))
      )

    interpEnv.add("b", Core.BoxedExpr.make(BoolSort(), boolVar))
    interpEnv.add("n", Core.BoxedExpr.make(NumericSort(), numVar))
    interpEnv.add("arr", Core.BoxedExpr.make(arrVar.sort, arrVar))
    interpEnv.add("f", Core.BoxedExpr.make(funVarSort, funVar))
    interpEnv.add("double", Core.BoxedExpr.make(doubleMacro.sort, doubleMacro))

    val testNs = new CozyNamespace(ns, typeEnv, interpEnv)
    CS.currentNS = testNs
  }

  override protected def afterAll(): Unit = {
    CS.currentNS = previousNs
    super.afterAll()
  }

  private def parse(expr: CozyExpr): Either[String, Core.BoxedExpr] =
    CozyToFormula.cozyParseExpr(expr)

  private def seq(args: CozyExpr*): CozyExpr =
    CozyExpr.CSeq(args.toVector)

  private def sym(name: String): CozyExpr =
    CozyExpr.CSymbol(name, "user")

  private def expectBool(expr: CozyExpr, expected: Core.Expr[BoolSort]): Unit =
    parse(expr) match {
      case Right(boxed) =>
        boxed.unify(BoolSort()) match {
          case Some(boolExpr) => assert(boolExpr == expected)
          case None => fail("expected boolean expression")
        }
      case Left(err) => fail(s"expected success but got $err")
    }

  private def expectNumeric(expr: CozyExpr, expected: Core.Expr[NumericSort]): Unit =
    parse(expr) match {
      case Right(boxed) =>
        boxed.unify(NumericSort()) match {
          case Some(numExpr) => assert(numExpr == expected)
          case None => fail("expected numeric expression")
        }
      case Left(err) => fail(s"expected success but got $err")
    }

  private def expectArray(expr: CozyExpr, expected: Core.Expr[ArraySort[NumericSort, NumericSort]]): Unit =
    parse(expr) match {
      case Right(boxed) =>
        boxed.unify(ArraySort(NumericSort(), NumericSort())) match {
          case Some(arrExpr) => assert(arrExpr == expected)
          case None => fail("expected array expression")
        }
      case Left(err) => fail(s"expected success but got $err")
    }

  private def assertLeft(expr: CozyExpr, fragment: String): Unit =
    parse(expr) match {
      case Left(msg) => assert(msg.contains(fragment))
      case Right(value) =>
        fail(s"expected failure but parsed ${value.e}")
    }

  test("parses literals, lookups and rejects missing symbols") {
    expectBool(CozyExpr.CBool(true), Core.mkTrue)
    expectNumeric(CozyExpr.CInt(7), Core.mkNumber(7))
    expectNumeric(sym("n"), numVar)
    assertLeft(sym("missing"), "variable missing not found")
    assertLeft(CozyExpr.CSeq(Vector.empty), "empty sequence")
  }

  test("boolean connectives, equality and implication") {
    expectBool(
      seq(sym("and"), sym("b"), CozyExpr.CBool(true)),
      Core.mkAnd(List(boolVar, Core.mkTrue))
    )
    expectBool(
      seq(sym("or"), CozyExpr.CBool(false), sym("b")),
      Core.mkOr(List(Core.mkFalse, boolVar))
    )
    expectBool(seq(sym("not"), CozyExpr.CBool(false)), Core.mkNot(Core.mkFalse))
    expectBool(
      seq(sym("="), CozyExpr.CInt(1), CozyExpr.CInt(1)),
      Core.mkEq(Core.mkNumber(1), Core.mkNumber(1))
    )
    assertLeft(seq(sym("="), CozyExpr.CInt(1), CozyExpr.CInt(1), CozyExpr.CInt(1)), "=")
    expectBool(
      seq(sym("=>"), sym("b"), CozyExpr.CBool(false)),
      Core.mkImplies(boolVar, Core.mkFalse)
    )
    expectNumeric(
      seq(sym("=>"), sym("b"), CozyExpr.CInt(1), CozyExpr.CInt(2)),
      Core.mkIte(boolVar, Core.mkNumber(1), Core.mkNumber(2))
    )
  }

  test("ite expressions combine conditionals and branches") {
    val cond = seq(sym("="), sym("n"), CozyExpr.CInt(0))
    val iteExpr = seq(sym("ite"), cond, CozyExpr.CInt(1), CozyExpr.CInt(2))
    expectNumeric(iteExpr, Core.mkIte(Core.mkEq(numVar, Core.mkNumber(0)), Core.mkNumber(1), Core.mkNumber(2)))
  }

  test("arithmetic operations include additive, multiplicative and negation variants") {
    expectNumeric(
      seq(sym("+"), CozyExpr.CInt(1), CozyExpr.CInt(2), CozyExpr.CInt(3)),
      Core.mkAdd(List(Core.mkNumber(1), Core.mkNumber(2), Core.mkNumber(3)))
    )
    expectNumeric(
      seq(sym("*"), CozyExpr.CInt(2), CozyExpr.CInt(4)),
      Core.mkMul(List(Core.mkNumber(2), Core.mkNumber(4)))
    )
    expectNumeric(seq(sym("-"), CozyExpr.CInt(5)), Core.mkNegative(Core.mkNumber(5)))
    expectNumeric(
      seq(sym("-"), sym("n"), CozyExpr.CInt(1), CozyExpr.CInt(2)),
      Core.mkMinus(numVar, Core.mkAdd(List(Core.mkNumber(1), Core.mkNumber(2))))
    )
  }

  test("comparison chains lower into conjunctions for all operators") {
    val builders = List[(String, (Core.Expr[NumericSort], Core.Expr[NumericSort]) => Core.Expr[BoolSort])](
      "<" -> ((a, b) => Core.mkLt(a, b)),
      "<=" -> ((a, b) => Core.mkLe(a, b)),
      ">" -> ((a, b) => Core.mkGt(a, b)),
      ">=" -> ((a, b) => Core.mkGe(a, b))
    )
    builders.foreach { case (op, mkCmp) =>
      val expr = seq(sym(op), CozyExpr.CInt(0), CozyExpr.CInt(1), CozyExpr.CInt(2))
      val expected = Core.mkAnd(List(mkCmp(Core.mkNumber(0), Core.mkNumber(1)), mkCmp(Core.mkNumber(1), Core.mkNumber(2))))
      expectBool(expr, expected)
    }
  }

  test("array select and store produce typed AST nodes") {
    expectNumeric(
      seq(sym("select"), sym("arr"), sym("n")),
      Core.mkSelect(arrVar, numVar)
    )
    expectArray(
      seq(sym("store"), sym("arr"), sym("n"), CozyExpr.CInt(42)),
      Core.mkStore(arrVar, numVar, Core.mkNumber(42))
    )
  }

  test("quantifiers introduce scoped binders") {
    val forallExpr =
      seq(
        sym("forall"),
        CozyExpr.CSeq(Vector(seq(sym("x"), sym("Int")))),
        seq(sym("=>"), seq(sym("<"), sym("x"), CozyExpr.CInt(10)), seq(sym(">="), sym("n"), sym("x")))
      )
    parse(forallExpr) match {
      case Right(boxed) =>
        boxed.e match {
          case Core.Forall(vars, body) =>
            assert(vars == List(("x", Core.numericSort)))
            assert(body == Core.mkImplies(Core.mkLt(Core.mkVar("x", NumericSort()), Core.mkNumber(10)), Core.mkGe(numVar, Core.mkVar("x", NumericSort()))))
          case other => fail(s"expected forall, got $other")
        }
      case Left(err) => fail(s"expected forall but got $err")
    }

    val existsExpr =
      seq(
        sym("exists"),
        CozyExpr.CSeq(Vector(seq(sym("y"), sym("Int")))),
        seq(sym("="), sym("y"), CozyExpr.CInt(5))
      )
    parse(existsExpr) match {
      case Right(boxed) =>
        boxed.e match {
          case Core.Exists(vars, body) =>
            assert(vars == List(("y", Core.numericSort)))
            assert(body == Core.mkEq(Core.mkVar("y", NumericSort()), Core.mkNumber(5)))
          case other => fail(s"expected exists, got $other")
        }
      case Left(err) => fail(s"expected exists but got $err")
    }
  }

  test("function calls work for uninterpreted functions and macros") {
    parse(seq(sym("f"), CozyExpr.CInt(1))) match {
      case Right(boxed) =>
        assert(boxed.sort == NumericSort())
      case Left(err) => fail(s"expected uninterpreted call, got $err")
    }

    parse(seq(sym("double"), CozyExpr.CInt(3))) match {
      case Right(boxed) =>
        assert(boxed.sort == NumericSort())
      case Left(err) => fail(s"expected macro call, got $err")
    }
  }

  test("unknown expressions surface descriptive failures") {
    assertLeft(seq(sym("bogus"), CozyExpr.CBool(true)), "function bogus not found")
  }
}
