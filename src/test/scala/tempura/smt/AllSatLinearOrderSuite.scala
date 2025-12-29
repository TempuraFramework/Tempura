package tempura.smt

import tempura.expression.Core.*
import org.scalatest.funsuite.AnyFunSuite
import tempura.expression.{Core, Syntax}

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


    // forall T, U, V.
    //  either not(T < U /\ U < V) or T < V
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

    List(transitiveOrder, antisymmetric, totalOrder, zeroLeast)
  }

  private case class AllSatFixture(cardinality: Int,
                                   solver: Z3Solver.Z3Solver,
                                   assertions: List[Core.Expr[Core.BoolSort]],
                                   vocab: Set[(String, Core.BoxedSort)])

  private def buildFixture(cardinality: Int): AllSatFixture = {
    require(cardinality >= 1, "Finite universe must have at least one element")

    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val timeSort = typeEnv |- FiniteUniverseSort("time", cardinality)

    val ltTimeSort = Core.FunSort(List(timeSort.box, timeSort.box), Core.BoolSort())
    val ltTimeFun = interpEnv |- ("<:time:time", ltTimeSort)
    val zeroTime = interpEnv |- ("0:time", timeSort)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val assertions = timeLinearOrderAxioms(timeSort, ltTimeFun, zeroTime)

    val vocab: Set[(String, Core.BoxedSort)] = Set(
      ("<:time:time", ltTimeSort.box),
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
    println(s" ******** Expected model count: ${expectedModelCount(2)}")

    val observed = runAllSatTest(2)
    assert(observed == expectedModelCount(2))
  }

  test("allSat linear order on time sort with cardinality 3") {
    val observed = runAllSatTest(3)
    assert(observed == expectedModelCount(3))
  }

  test("allSat with cardinality 4") {
    val observed = runAllSatTest(4)
    assert(observed == expectedModelCount(4))
  }

  test("printing model counts") {
    (1 until 10).foreach(x =>
    println(s"${x} -> ${expectedModelCount(x)}"))
  }
}
