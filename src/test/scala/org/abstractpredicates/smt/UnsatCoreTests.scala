package org.abstractpredicates.smt

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.smt.SmtSolver.Result
import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.expression.Syntax.intToNumber

class UnsatCoreTests extends AnyFunSuite {

  private case class SolverTestEnv(
    name: String,
    typeEnv: Core.TypeEnv,
    interpEnv: Core.InterpEnv,
    solver: SmtSolver.Solver[?, ?]
  )

  private case class Scenario(
    formulas: List[Core.Expr[Core.BoolSort]],
    mustAppear: Set[Core.Expr[Core.BoolSort]]
  )

  private case class SolverFactory(name: String, build: () => SolverTestEnv)

  private val solverFactories: List[SolverFactory] = List(
    SolverFactory("Z3", () => {
      val typeEnv = Core.emptyTypeEnv
      val interpEnv = Core.emptyInterpEnv
      val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
      solver.initialize(SmtSolver.allLia)
      SolverTestEnv("Z3", typeEnv, interpEnv, solver)
    }),
    SolverFactory("SmtInterpol", () => {
      val typeEnv = Core.emptyTypeEnv
      val interpEnv = Core.emptyInterpEnv
      val solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
      solver.initialize(SmtSolver.allLia)
      SolverTestEnv("SmtInterpol", typeEnv, interpEnv, solver)
    }),
    SolverFactory("CVC5", () => {
      val typeEnv = Core.emptyTypeEnv
      val interpEnv = Core.emptyInterpEnv
      val solver = Cvc5Solver.Cvc5Solver(typeEnv, interpEnv)
      solver.initialize(SmtSolver.allLia)
      SolverTestEnv("CVC5", typeEnv, interpEnv, solver)
    })
  )

  private def runUnsatCoreScenario(label: String)(setup: SolverTestEnv => Scenario): Unit = {
    solverFactories.foreach { factory =>
      val env = factory.build()
      val scenario = setup(env)

      env.solver.add(scenario.formulas.map(_.box()))
      val result = env.solver.checkSat()
      assert(result == Result.UNSAT, s"[${label}] ${env.name}: expected UNSAT but solver reported $result")

      val coreOpt = env.solver.getUnsatCore
      assert(coreOpt.isDefined, s"[${label}] ${env.name}: expected an unsat core but solver returned none")

      val coreFormulas = coreOpt.get.formulas()
      assert(coreFormulas.nonEmpty, s"[${label}] ${env.name}: unsat core should not be empty")

      val originalFormulas = scenario.formulas.toSet
      assert(
        coreFormulas.subsetOf(originalFormulas),
        s"[${label}] ${env.name}: unsat core formulas must be drawn from the asserted set"
      )

      scenario.mustAppear.foreach { expected =>
        assert(
          coreFormulas.contains(expected),
          s"[${label}] ${env.name}: expected unsat core to contain ${expected}"
        )
      }
    }
  }

  private def guardedLinearScenario(testEnv: SolverTestEnv): Scenario = {
    val interp = testEnv.interpEnv

    val x = interp |- ("x", Core.numericSort)
    val guard = interp |- ("guard", Core.boolSort)

    // System of constraints:
    // (1) guard = T
    // (2) guard => (x >= 8)
    // (3) x <= 2
    // (4) x >= 0

    val guardActive = guard
    val guardForcesLarge = guard |= (x >= 8) // Core.mkImplies(guard, Core.mkGe(x, Core.mkNumber(8)))
    val smallUpperBound = x <= 2 // Core.mkLe(x, Core.mkNumber(2))
    val nonNegative = x >= 0 // Core.mkGe(x, Core.mkNumber(0))

    println(s"list of formulas: ${List(guardActive, guardForcesLarge, smallUpperBound, nonNegative).mkString("\n")}")

    Scenario(
      formulas = List(guardActive, guardForcesLarge, smallUpperBound, nonNegative),
      mustAppear = Set(guardActive, guardForcesLarge, smallUpperBound)
    )
  }

  private def arrayStoreScenario(testEnv: SolverTestEnv): Scenario = {
    val interp = testEnv.interpEnv

    val arraySort = Core.ArraySort(Core.NumericSort(), Core.NumericSort())
    val arr = Core.mkVar("arr", arraySort)
    val idx = Core.mkVar("idx", Core.NumericSort())
    interp.add("arr", arr)
    interp.add("idx", idx)

    val selfUpdate = Core.mkEq(arr, Core.mkStore(arr, idx, Core.mkNumber(1)))
    val conflictingRead = Core.mkEq(Core.mkSelect(arr, idx), Core.mkNumber(0))
    val pinnedIndex = Core.mkEq(idx, Core.mkNumber(3))
    val stability = Core.mkEq(Core.mkSelect(arr, Core.mkNumber(5)), Core.mkSelect(arr, Core.mkNumber(5)))

    Scenario(
      formulas = List(selfUpdate, conflictingRead, pinnedIndex, stability),
      mustAppear = Set(selfUpdate, conflictingRead)
    )
  }

  private def datatypePaletteScenario(testEnv: SolverTestEnv): Scenario = {
    val tEnv = testEnv.typeEnv
    val iEnv = testEnv.interpEnv

    val redCtor = Core.constructor("Red", List())
    val greenCtor = Core.constructor("Green", List())
    val colorSortBoxed = Core.datatypeSort("Color", List(redCtor, greenCtor))
    tEnv.add("Color", colorSortBoxed)

    val colorSort = colorSortBoxed.sort
    val palette = Core.mkVar("palette", Core.ArraySort(Core.BoolSort(), colorSort))
    val chosen = Core.mkVar("chosenColor", colorSort)
    iEnv.add("palette", palette)
    iEnv.add("chosenColor", chosen)

    val redValue = Core.mkDatatypeAccessor(colorSort, Core.instantiatedConstructor(redCtor, List()))
    val greenValue = Core.mkDatatypeAccessor(colorSort, Core.instantiatedConstructor(greenCtor, List()))
    val valueAtTrue = Core.mkSelect(palette, Core.mkTrue)
    val valueAtFalse = Core.mkSelect(palette, Core.mkFalse)

    val trueIsRed = Core.mkEq(valueAtTrue, redValue)
    val falseIsGreen = Core.mkEq(valueAtFalse, greenValue)
    val unifiedCells = Core.mkEq(valueAtTrue, valueAtFalse)
    val chosenTracksTrue = Core.mkEq(chosen, valueAtTrue)

    Scenario(
      formulas = List(trueIsRed, falseIsGreen, unifiedCells, chosenTracksTrue),
      mustAppear = Set(trueIsRed, falseIsGreen, unifiedCells)
    )
  }

  test("unsat core with boolean and linear constraints") {
    runUnsatCoreScenario("boolean-guarded linear contradiction")(guardedLinearScenario)
  }

  test("unsat core with arrays") {
    runUnsatCoreScenario("array store/read contradiction")(arrayStoreScenario)
  }

  test("unsat core with datatype sorts") {
    runUnsatCoreScenario("datatype palette inconsistency")(datatypePaletteScenario)
  }
}
