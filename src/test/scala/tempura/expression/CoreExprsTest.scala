package tempura.expression

import org.scalatest.funsuite.AnyFunSuite
import Core.*
import Core.NumericSort.*
import Core.BoolSort.*
import tempura.expression.transforms.{LetRemover, MacroExpander, Visitor}

class CoreExprsTest extends AnyFunSuite {
  // -- helpers ---------------------------------------------------------------
  private val emptyEnv = Core.emptyInterpEnv

  private def num(n: Int): Expr[NumericSort] =
    Core.mkConst(SortValue.NumericValue(n))

  private def bool(b: Boolean): Expr[BoolSort] =
    Core.mkConst(SortValue.BoolValue(b))

  // instantiate the partial evaluator
  private val visitor = new Visitor()

  // -- var‐lookup ------------------------------------------------------------
  test("VarNumeric: found in env") {
    val x = Core.mkVar("x", NumericSort())
    val env = Core.emptyInterpEnv
    env.add("x", num(7))
    assert(visitor.visit(env)(x) == num(7))
  }
  test("VarNumeric: not in env") {
    val x = Core.mkVar("x", NumericSort())
    assert(visitor.visit(emptyEnv)(x) == x)
  }
  test("VarBool: found / not found") {
    val b = Core.mkVar("b", BoolSort())
    val env = Core.emptyInterpEnv
    env.add("b", bool(true))
    assert(visitor.visit(env)(b) == bool(true))
    assert(visitor.visit(emptyEnv)(b) == b)
  }

  // -- arithmetic -----------------------------------------------------------
  test("Plus/Minus/Multiply/Divide on constants") {
    val a = num(10)
    val b = num(3)
    assert(visitor.visit(emptyEnv)(Core.mkAdd(List(num(10), num(3)))) == num(13))
    assert(visitor.visit(emptyEnv)(Core.mkMinus(num(10), num(3))) == num(7))
    assert(visitor.visit(emptyEnv)(Core.mkMul(List(num(10), num(3)))) == num(30))
    assert(visitor.visit(emptyEnv)(Core.mkFraction(num(10), num(3))) == num(3))
  }

  // -- boolean ops ----------------------------------------------------------
  test("And/Or/Not on constants") {
    assert(visitor.visit(emptyEnv)(Core.mkAnd(List(bool(true), bool(false)))) == bool(false))
    assert(visitor.visit(emptyEnv)(Core.mkOr(List(bool(true), bool(false)))) == bool(true))
    assert(visitor.visit(emptyEnv)(Core.mkNot(bool(true))) == bool(false))
  }

  // -- Ite / Equality -------------------------------------------------------
  test("Ite true/false branches") {
    val zero = num(0)
    val one = num(1)
    val two = num(2)
    val condTrue = Core.mkEq(zero, zero)
    val condFalse = Core.mkEq(zero, one)
    assert(visitor.visit(emptyEnv)(Core.mkIte(condTrue, one, two)) == one)
    assert(visitor.visit(emptyEnv)(Core.mkIte(condFalse, one, two)) == two)
  }
  test("Equality differing vs equal") {
    assert(visitor.visit(emptyEnv)(Core.mkEq(num(5), num(5))) == bool(true))
    assert(visitor.visit(emptyEnv)(Core.mkEq(num(5), num(6))) == bool(false))
  }

  // -- Let-binding ----------------------------------------------------------
  test("Let binding substitutes and evaluates") {
    // let x = 3 in x+2  ==> 5
    val letExpr = Core.mkSubst("let", List(("x", num(3))),
      Core.mkMacro("let-app", List(("x", Core.NumericSort())), Core.mkAdd(List(Core.mkVar("x", NumericSort()), num(2))))
    )
    val letRemover = new LetRemover()
    assert(letRemover.visit(emptyEnv)(letExpr) == num(5))
  }

  // -- Fun / App (identity) ------------------------------------------------
  test("identity function") {
    val id = Core.mkMacro("id", List(("x", Core.NumericSort())), Core.mkVar("x", NumericSort()))
    val in = num(99)
    val macroExpander = new MacroExpander()
    assert(macroExpander.visit(emptyEnv)(id) == id)
  }

  test("sort comparison") {
    val s0a = Core.UnInterpretedSort("s0", 0).box
    val s0b = Core.UnInterpretedSort("s0", 0).box
    val s1 = Core.UnInterpretedSort("s1", 0).box
    val s0c = Core.UnInterpretedSort("s0", 1).box
    assert(s0a == s0b && s0a != s1 && s0a != s0c)

    val map = Map("s0" -> s0a)

    assert(s0a == map("s0") && s0b == map("s0"))
  }

  test("value comparison") {
    val x0a = SortValue.NumericValue(0)
    val x0b = SortValue.NumericValue(0)
    assert(x0a == x0b, "Test A failed")

    val y0a = Core.mkConst(SortValue.NumericValue(0))
    val y0b = Core.mkConst(SortValue.NumericValue(0))
    assert(y0a == y0b, "Test B failed")

    val v0a = Core.mkConst(SortValue.NumericValue(0)).box()
    val v0b = Core.mkConst(SortValue.NumericValue(0)).box()
    assert(v0a == v0b, "Test C failed")
  }

  // -- BinOp / UnOp / TerOp -------------------------------------------------
  /*test("BinOp & UnOp & TerOp") {
    val bin = BinOp(bool(true), bool(false), (x: Expr[BoolSort]) => (y: Expr[BoolSort]) => And(x, y))
    assert(visitor.eval(emptyEnv)(bin) == bool(false))

    val un = UnOp(bool(false), (x: Expr[BoolSort]) => Not(x))
    assert(visitor.eval(emptyEnv)(un) == bool(true))

    val ter = TerOp(num(1), num(2), num(3),
      (a: Expr[NumericSort]) => (b: Expr[NumericSort]) => (c: Expr[NumericSort]) =>
        Plus(Plus(a, b), c))
    assert(visitor.eval(emptyEnv)(ter) == num(6))
  }

  /** helper to make a Bool constant */
  private def b(b: Boolean): Expr[BoolSort] =
    ConstBool(if b then BTrue else BFalse)

  test("Forall-1") {
    // ∀x. ¬x
    val notAll = Forall { (x: Expr[BoolSort]) =>
      Not(x)
    }

    // applying to true should give ¬true
    val appTrue = visitor.eval(Env.empty)(App(notAll, b(true)))
    assert(appTrue == ConstBool(BFalse))

    // applying to false should give ¬false
    val appFalse = visitor.eval(Env.empty)(App(notAll, b(false)))
    assert(appFalse == ConstBool(BTrue))
  }

  test("Exists-1") {
    // ∀x. ¬x
    val notAll = Exists { (x: Expr[BoolSort]) =>
      Not(x)
    }

    // applying to true should give ¬true
    val appTrue = visitor.eval(Env.empty)(App(notAll, b(true)))
    assert(appTrue == ConstBool(BFalse))

    // applying to false should give ¬false
    val appFalse = visitor.eval(Env.empty)(App(notAll, b(false)))
    assert(appFalse == ConstBool(BTrue))
  }

  test("Exists-2") {
    // ∃x. x ∨ false  ≡ λx. x  (since x∨false = x)
    val existsOrFalse = Exists { (x: Expr[BoolSort]) =>
      Or(x, b(false))
    }

    val appT = visitor.eval(emptyEnv)(App(existsOrFalse, b(true)))
    assert(appT == ConstBool(BTrue))

    val appF = visitor.eval(emptyEnv)(App(existsOrFalse, b(false)))
    assert(appF == ConstBool(BFalse))
  }

  test("Nested quantifier elimination -- 0") {
    // ∀x. ∀y. x ∧ y
    val forallAnd: Expr[BoolSort => (BoolSort => BoolSort)] =
      Fun { (x: Expr[BoolSort]) =>
        Fun { (y: Expr[BoolSort]) =>
          And(x, y)
        }
      }

    // apply both quantifiers in one go
    val nestedApp =
      App(App(forallAnd, b(true)), b(false))

    // should be And(true, false)
    assert(visitor.eval(emptyEnv)(nestedApp) == ConstBool(BFalse))

    // similarly, you could write:
    // val partial = App(forallAnd, b(true))   // a function Expr[Bool] => Expr[Bool]
    // val final  = App(partial, b(false))
    // assert(final == And(b(true), b(false)))
  }
  test("Nested quantifier elimination -- 1") {
    // ∀x. ∀y. x ∧ y
    val forallAnd: Expr[BoolSort => (BoolSort => BoolSort)] =
      PForall { (x: Expr[BoolSort]) =>
        Forall { (y: Expr[BoolSort]) =>
          And(x, y)
        }
      }
    // apply both quantifiers in one go
    val nestedApp =
      App(App(forallAnd, b(true)), b(false))

    // should be And(true, false)
    assert(visitor.eval(emptyEnv)(nestedApp) == ConstBool(BFalse))

    // similarly, you could write:
    // val partial = App(forallAnd, b(true))   // a function Expr[Bool] => Expr[Bool]
    // val final  = App(partial, b(false))
    // assert(final == And(b(true), b(false)))
  }*/
}