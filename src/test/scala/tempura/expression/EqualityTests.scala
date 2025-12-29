package tempura.expression

import org.scalatest.funsuite.AnyFunSuite
import Core.*
import Core.SortValue.*

class EqualityTests extends AnyFunSuite {

  //
  // 1) BoxedExpr ↔ Expr equality asymmetry (and boxed-const equality failure)
  //

  test("BoxedExpr == BoxedExpr should be true for identical underlying Expr") {
    val v0a = Core.mkConst(NumericValue(0)).box()
    val v0b = Core.mkConst(NumericValue(0)).box()
    assert(v0a == v0b && v0a == v0b.unbox && v0a.unbox == v0b)
  }

  test("BoxedExpr ↔ Expr ") {
    val expr = Core.mkConst(NumericValue(1))
    val boxed = expr.box()
    // Currently v == e is true (Expr compares to Expr), but e == v is false (Expr doesn't know BoxedExpr)
    assert(boxed == expr, "boxed == expr")
    assert(expr == boxed, "expr == boxed")
  }

  //
  // 2) BoxedSort ↔ Sort equality asymmetry
  //

  test("BoxedSort ↔ Sort") {
    val s: NumericSort = NumericSort()
    val bs = Core.numericSort // BoxedSort { type S = NumericSort }
    assert(bs == s, "Forward test")
    assert(s == bs, "Reverse test")

    val s1: BoolSort = BoolSort()
    val bs1 : BoxedSort = Core.boolSort

    assert(bs1 == s1, "Forward test")
    assert(s1 == bs1, "Reverse test")

    val arr1 = Core.arraySort(Core.BoolSort(), Core.arraySort(Core.NumericSort(), Core.NumericSort()))
    val arr2 = Core.arraySort(Core.BoolSort(), Core.arraySort(Core.BoolSort(), Core.NumericSort()))
    val arr1B = Core.ArraySort(Core.BoolSort(), Core.arraySort(Core.NumericSort(), Core.NumericSort()))
    assert(arr1 != arr2, "Forward test")
    assert(arr2 != arr1, "Reverse test")
    assert(arr1 == arr1B, "Forward test")
    assert(arr1B == arr1, "Reverse test")

    val fun1 = Core.funSort(List(Core.BoolSort(), Core.ArraySort(Core.NumericSort(), Core.NumericSort())), Core.NumericSort())
    val fun2 = Core.funSort(List(Core.BoolSort(), Core.ArraySort(Core.BoolSort(), Core.NumericSort())), Core.NumericSort())
    val fun3a = Core.funSort(List(Core.BoolSort()), Core.NumericSort())
    val fun3b = Core.FunSort(List(Core.BoolSort()), Core.numericSort)
    val fun1B = Core.FunSort(List(Core.BoolSort(), Core.ArraySort(Core.NumericSort(), Core.NumericSort())), Core.NumericSort())

    assert(fun1 != fun2, "Forward test")
    assert(fun2 != fun1, "Reverse test")
    assert(fun1 == fun1B, "Forward test")
    assert(fun1B == fun1, "Reverse test")
    assert(fun1 != fun3a && fun2 != fun3a && fun3a != fun1 && fun3a != fun2, "domain test a")
    assert(fun1 != fun3b && fun2 != fun3b && fun3b != fun1 && fun3b != fun2, "domain test b")
    assert(fun3a == fun3b && fun3b == fun3a, "Domain length test")

    val u0 = Core.UnInterpretedSort("U", 0)
    val u0b = Core.uSort("U", 0)
    val u1 = Core.UnInterpretedSort("U", 1)
    val u1b = Core.uSort("U", 1)
    assert(u0 == u0b, "Forward test")
    assert(u0b == u0, "Reverse test")
    assert(u0 != u1b && u1b != u0, "Forward test")
    assert(u0 != u1 && u1 != u0, "Reverse test")

    val cons0 = Core.constructor("C", List())
    val cons1 = Core.constructor("C", List(("a", Core.numericSort)))
    assert(cons0 != cons1 && cons1 != cons0)

    val ic0 = Core.InstantiatedConstructor(cons0, List())
    val ic1 = Core.InstantiatedConstructor(cons1, List())
    val ic1b = Core.InstantiatedConstructor(cons1, List(Core.mkConst(1)))
    assert(ic0 != ic1 && ic0 != cons0 && ic1 != ic0 && ic1 != ic1b && ic1b != ic1 && ic1b != ic0)

    val dt0 = Core.DatatypeConstructorSort("T", List(cons0))
    val dt1 = Core.DatatypeConstructorSort("T", List(cons1))
    val dt1b = Core.DatatypeConstructorSort("T", List(cons1, cons0))
    val dt0b = Core.DatatypeConstructorSort("T", List(cons0)).box
    assert(dt0 != dt1)
    assert(dt1 != dt0)
    assert(dt1 != dt1b && dt1b != dt1)
    assert(dt1b != dt0 && dt0 != dt1b)
    assert(dt0b != dt1b && dt1b != dt0b)
    assert(dt0b == dt0 && dt0 == dt0b)

    val ps = Core.uSort("Parametrized", 2)
    val alias0 = Core.AliasSort("A", List(Core.numericSort), Core.numericSort)
    val alias0b = alias0.box
    assert(alias0 == alias0b && alias0b == alias0)
  }

  test("BoxedSort in collections membership") {
    val s: BoolSort = BoolSort()
    val bs = Core.boolSort

    val setOfBoxed = Set(bs)
    val setOfSorts = Set(s)

    assert(setOfBoxed.contains(s))
    assert(setOfSorts.contains(bs))
  }

  test("AliasSort.equals should consider args ") {
    // different arg lists
    val argA = List(Core.numericSort)
    val argB = List(Core.numericSort)

    val a1 = Core.AliasSort("A", argA, Core.NumericSort())
    val a2 = Core.AliasSort("A", argB, Core.BoolSort())

    assert(a1 != a2 && (a1 == Core.AliasSort("A", argB, Core.NumericSort())))
  }


  test("UnInterpretedSort hashCode") {
    val u1 = Core.UnInterpretedSort("U", 1)
    val u2 = Core.UnInterpretedSort("U", 2)
    assert(u1 != u2)
    assert(u1.hashCode != u2.hashCode)
  }

  test("FiniteUniverseSort hashCode") {
    val f1 = Core.FiniteUniverseSort("F", 3)
    val f2 = Core.FiniteUniverseSort("F", 7)
    assert(f1 != f2)
    assert(f1.hashCode != f2.hashCode)
  }

  test("DatatypeConstructorSort: hashCode") {
    val c1 = Core.constructor("C", Nil)
    val c2 = Core.constructor("D", Nil)

    val dt1 = Core.DatatypeConstructorSort("T", List(c1))
    val dt2 = Core.DatatypeConstructorSort("T", List(c2))

    assert(dt1 != dt2)
    // Current hashCode uses only 'name'
    assert(dt1.hashCode != dt2.hashCode)
  }


  test("SortValue equality") {
    val x0a = NumericValue(0)
    val x0b = NumericValue(0)
    assert(x0a == x0b)
  }

  test("Expr(Const(...)) equality") {
    val y0a = Core.mkConst(NumericValue(0))
    val y0b = Core.mkConst(NumericValue(0))
    assert(y0a == y0b)
  }

  test("BoxedExpr equality") {
    val v0a = Core.mkConst(NumericValue(0)).box()
    val v0b = Core.mkConst(NumericValue(0)).box()
    assert(v0a == v0b)
  }
}