package org.abstractpredicates.smt

import org.abstractpredicates.expression.{Core, Syntax}
import org.abstractpredicates.expression.Core.*
import org.scalatest.funsuite.AnyFunSuite

class AllSatLinearOrderSuite extends AnyFunSuite {

  import Syntax.*

  private def factorial(n: Int): Int =
    if n <= 1 then 1 else (2 to n).product

  private def expectedModelCount(cardinality: Int): Int = {
    val pairs = cardinality - 1
    factorial(cardinality) * (1 << pairs)
  }

  private def timeLinearOrderAxioms(timeSort: Core.FiniteUniverseSort,
                                    ltFun: Core.Expr[Core.FunSort[Core.BoolSort]],
                                    succFun: Core.Expr[Core.FunSort[Core.BoolSort]],
                                    zero: Core.Expr[Core.FiniteUniverseSort]): List[Core.Expr[Core.BoolSort]] = {

    def vars(names: String*): List[(String, Core.BoxedSort)] =
      names.toList.map(name => (name, timeSort.box))

    def v(name: String): Core.Expr[Core.FiniteUniverseSort] =
      Core.mkVar(name, timeSort)

    def app(fun: Core.Expr[Core.FunSort[Core.BoolSort]],
            args: Core.Expr[Core.FiniteUniverseSort]*): Core.Expr[Core.BoolSort] =
      val bindings = args.zipWithIndex.map { case (arg, idx) => (s"arg_$idx", arg.box()) }.toList
      Core.mkSubst("app", bindings, fun)

    def lt(lhs: Core.Expr[Core.FiniteUniverseSort], rhs: Core.Expr[Core.FiniteUniverseSort]): Core.Expr[Core.BoolSort] =
      app(ltFun, lhs, rhs)

    def succ(lhs: Core.Expr[Core.FiniteUniverseSort], rhs: Core.Expr[Core.FiniteUniverseSort]): Core.Expr[Core.BoolSort] =
      app(succFun, lhs, rhs)

    val immediateSuccessor =
      Core.mkForall(
        vars("X", "Y", "Z"),
        Core.mkNot(succ(v("X"), v("Z"))) \/
          (lt(v("X"), v("Z")) /\ Core.mkNot(lt(v("X"), v("Y")) /\ lt(v("Y"), v("Z"))))
      )

    val transitiveOrder =
      Core.mkForall(
        vars("T", "U", "V"),
        Core.mkNot(lt(v("T"), v("U")) /\ lt(v("U"), v("V"))) \/ lt(v("T"), v("V"))
      )

    val antisymmetric =
      Core.mkForall(
        vars("T", "U"),
        Core.mkNot(lt(v("T"), v("U")) /\ lt(v("U"), v("T")))
      )

    val totalOrder =
      Core.mkForall(
        vars("T", "U"),
        lt(v("T"), v("U")) \/
          Core.mkEq(v("T"), v("U")) \/
          lt(v("U"), v("T"))
      )

    val zeroLeast =
      Core.mkForall(
        vars("X0"),
        Core.mkEq(zero, v("X0")) \/ lt(zero, v("X0"))
      )

    List(immediateSuccessor, transitiveOrder, antisymmetric, totalOrder, zeroLeast)
  }

  private case class AllSatFixture(cardinality: Int,
                                   solver: Z3Solver.Z3Solver,
                                   assertions: List[Core.Expr[Core.BoolSort]],
                                   vocab: Set[(String, Core.BoxedSort)])

  private def buildFixture(cardinality: Int): AllSatFixture = {
    require(cardinality >= 1, "Finite universe must have at least one element")

    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val timeSort = Core.FiniteUniverseSort("time", cardinality)
    typeEnv.add("time", timeSort)

    val ltTimeSort = Core.FunSort(List(timeSort.box, timeSort.box), Core.BoolSort())
    val succTimeSort = Core.FunSort(List(timeSort.box, timeSort.box), Core.BoolSort())
    val ltTimeFun = Core.mkVar("<:time:time", ltTimeSort)
    val timeSuccFun = Core.mkVar("time.succ", succTimeSort)
    val zeroTime = Core.mkVar("0:time", timeSort)
    interpEnv.add("<:time:time", ltTimeFun)
    interpEnv.add("time.succ", timeSuccFun)
    interpEnv.add("0:time", zeroTime)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.arithFree)

    val assertions = timeLinearOrderAxioms(timeSort, ltTimeFun, timeSuccFun, zeroTime)

    val vocab: Set[(String, Core.BoxedSort)] = Set(
      ("<:time:time", ltTimeSort.box),
      ("time.succ", succTimeSort.box),
      ("0:time", timeSort.box)
    )

    AllSatFixture(cardinality, solver, assertions, vocab)
  }

  private def runAllSatTest(cardinality: Int): Int = {
    val fixture = buildFixture(cardinality)
    fixture.assertions.foreach(expr => fixture.solver.add(List(expr.box())))
    val models = fixture.solver.allSat(fixture.vocab)
    models.length
  }

  test("allSat linear order on time sort with cardinality 1") {
    val observed = runAllSatTest(1)
    assert(observed == expectedModelCount(1))
  }

  test("allSat linear order on time sort with cardinality 2") {
    val observed = runAllSatTest(2)
    assert(observed == expectedModelCount(2))
  }

  test("allSat linear order on time sort with cardinality 3") {
    val observed = runAllSatTest(3)
    assert(observed == expectedModelCount(3))
  }
}
