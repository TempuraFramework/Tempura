package org.abstractpredicates.transitions

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.smt.Z3Solver

/**
 * Test suite for ForwardsFixpoint explicit-state model checker.
 *
 * Tests cover:
 * - Simple boolean transition systems
 * - Bounded counter systems
 * - Invariant checking
 * - Reachability analysis
 */
class ForwardsFixpointTest extends AnyFunSuite {
/*
  /**
   * Helper: Create a simple two-state boolean transition system
   *
   * State: x (boolean)
   * Init: ¬x
   * Trans: x' = ¬x (toggle)
   *
   * This should produce exactly 2 states: {x=false} and {x=true}
   * with edges forming a cycle.
   */
  def createToggleSystem(): (TransitionSystem, Z3Solver.Z3Solver) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())

    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    val init = Core.mkNot(x)
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val trs = TransitionSystem(
      stateVars = List(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    (trs, solver)
  }

  /**
   * Helper: Create a 2-bit counter system
   *
   * States: b0, b1 (booleans representing a 2-bit counter)
   * Init: b0 = false, b1 = false (count = 0)
   * Trans: increment modulo 4
   *   next_b0 = ¬b0
   *   next_b1 = b1 XOR b0
   *
   * States: 00 -> 10 -> 01 -> 11 -> 00 (cycle of length 4)
   */
  def createCounterSystem(): (TransitionSystem, Z3Solver.Z3Solver) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val b0 = interpEnv.newVar("b0", Core.BoolSort())
    val b1 = interpEnv.newVar("b1", Core.BoolSort())
    val next_b0 = interpEnv.newVar("next_b0", Core.BoolSort())
    val next_b1 = interpEnv.newVar("next_b1", Core.BoolSort())

    val timedVar0 = TimedVariable("b0", "next_b0", 0, Core.BoolSort())
    val timedVar1 = TimedVariable("b1", "next_b1", 0, Core.BoolSort())

    // Init: both bits are false (counter = 0)
    val init = Core.mkAnd(List(Core.mkNot(b0), Core.mkNot(b1)))

    // Transition: increment counter
    // next_b0 = ¬b0 (flip low bit)
    // next_b1 = b1 XOR b0 (carry: flip high bit when low bit wraps from 1 to 0)
    val trans = Core.mkAnd(List(
      Core.mkEq(next_b0, Core.mkNot(b0)),
      Core.mkEq(next_b1,
        Core.mkOr(List(
          Core.mkAnd(List(b1, Core.mkNot(b0))),
          Core.mkAnd(List(Core.mkNot(b1), b0))
        ))
      )
    ))

    val trs = TransitionSystem(
      stateVars = List(timedVar0, timedVar1),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    (trs, solver)
  }

  /**
   * Helper: Create a simple mutex system
   *
   * States: p0, p1 (booleans representing processes in critical section)
   * Init: ¬p0 ∧ ¬p1
   * Trans: (p0' = ¬p0 ∧ p1' = p1) ∨ (p0' = p0 ∧ p1' = ¬p1)
   *        (one process enters/leaves at a time)
   *
   * Invariant: ¬(p0 ∧ p1) (mutual exclusion)
   */
  def createMutexSystem(): (TransitionSystem, SolverEnvironment, Core.Expr[Core.BoolSort]) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val p0 = interpEnv.newVar("p0", Core.BoolSort())
    val p1 = interpEnv.newVar("p1", Core.BoolSort())
    val next_p0 = interpEnv.newVar("next_p0", Core.BoolSort())
    val next_p1 = interpEnv.newVar("next_p1", Core.BoolSort())

    val timedVar0 = TimedVariable("p0", "next_p0", 0, Core.BoolSort())
    val timedVar1 = TimedVariable("p1", "next_p1", 0, Core.BoolSort())

    // Init: neither process in critical section
    val init = Core.mkAnd(List(Core.mkNot(p0), Core.mkNot(p1)))

    // Trans: one process toggles, other stays the same
    val trans = Core.mkOr(List(
      Core.mkAnd(List(
        Core.mkEq(next_p0, Core.mkNot(p0)),
        Core.mkEq(next_p1, p1)
      )),
      Core.mkAnd(List(
        Core.mkEq(next_p0, p0),
        Core.mkEq(next_p1, Core.mkNot(p1))
      ))
    ))

    val trs = TransitionSystem(
      stateVars = List(timedVar0, timedVar1),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv).box

    // Mutual exclusion property: ¬(p0 ∧ p1)
    val mutexProperty = Core.mkNot(Core.mkAnd(List(p0, p1)))

    (trs, solver, mutexProperty)
  }

  test("toggle system: basic exploration") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(10)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    println(s"Toggle system statistics:\n${stats}")

    // Should have exactly 2 states
    assert(stats.totalStates == 2, s"Expected 2 states, got ${stats.totalStates}")

    // Should have 2 edges (forming a cycle)
    assert(stats.totalEdges == 2, s"Expected 2 edges, got ${stats.totalEdges}")
  }

  test("counter system: reachable states") {
    val (trs, solver) = createCounterSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(20)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    println(s"Counter system statistics:\n${stats}")

    // Should have exactly 4 states (2-bit counter: 00, 01, 10, 11)
    assert(stats.totalStates == 4, s"Expected 4 states, got ${stats.totalStates}")

    // Should have 4 edges (forming a cycle)
    assert(stats.totalEdges == 4, s"Expected 4 edges, got ${stats.totalEdges}")
  }

  test("mutex system: invariant holds") {
    val (trs, solver, mutexProperty) = createMutexSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.setMaxSteps(20)
    fixpoint.run()

    // Check that mutual exclusion holds in all reachable states
    val invariantHolds = fixpoint.checkInvariant(mutexProperty)

    assert(invariantHolds, "Mutual exclusion invariant should hold")
  }

  test("mutex system: reachable states") {
    val (trs, solver, _) = createMutexSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.setMaxSteps(20)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    println(s"Mutex system statistics:\n${stats}")

    // Should have exactly 3 states: (0,0), (1,0), (0,1)
    // State (1,1) is unreachable due to mutual exclusion
    assert(stats.totalStates == 3, s"Expected 3 states, got ${stats.totalStates}")
  }

  test("toggle system: initial states computation") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.computeInitialStates()

    // Should have exactly 1 initial state
    assert(initStates.size == 1, s"Expected 1 initial state, got ${initStates.size}")
  }

  test("counter system: initial states computation") {
    val (trs, solver) = createCounterSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.computeInitialStates()

    // Should have exactly 1 initial state (00)
    assert(initStates.size == 1, s"Expected 1 initial state, got ${initStates.size}")
  }

  test("toggle system: step-by-step exploration") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.computeInitialStates()

    assert(initStates.size == 1, "Should have 1 initial state")

    // Explore should find the second state
    fixpoint.setMaxSteps(5)
    fixpoint.explore()

    val stats = fixpoint.getStatistics
    assert(stats.totalStates == 2, s"After exploration, should have 2 states, got ${stats.totalStates}")
  }

  test("toggle system: max steps limit") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    // Set max steps to 0 - should only compute initial states
    fixpoint.setMaxSteps(0)
    fixpoint.run()

    val stats = fixpoint.getStatistics
    assert(stats.totalStates == 1, s"With maxSteps=0, should have 1 state, got ${stats.totalStates}")
    assert(stats.explorationSteps == 0, s"Should have 0 exploration steps, got ${stats.explorationSteps}")
  }

  test("empty initial states: no exploration") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())
    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    // Unsatisfiable initial condition
    val init = Core.mkAnd(List(x, Core.mkNot(x)))
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val trs = TransitionSystem(
      stateVars = List(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List())

    fixpoint.setMaxSteps(10)
    fixpoint.run()

    val stats = fixpoint.getStatistics
    assert(stats.totalStates == 0, "Should have 0 states with unsatisfiable init")
  }

  test("theory axioms: constrained exploration") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())
    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    // Init: true (any value)
    val init = Core.mkTrue

    // Trans: x' = ¬x
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val trs = TransitionSystem(
      stateVars = List(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    // Theory axiom: x must be false
    val theoryAxiom = Core.mkNot(x)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = ForwardsFixpoint[Z3Solver.Z3Solver](trs, solver, List(theoryAxiom))

    fixpoint.setMaxSteps(10)
    fixpoint.run()

    val stats = fixpoint.getStatistics

    // With theory axiom x = false, should only find state where x = false
    // But transition would lead to x = true, which violates theory
    // So should have 1 state with 0 successors
    assert(stats.totalStates == 1, s"Expected 1 state, got ${stats.totalStates}")
    assert(stats.totalEdges == 0, s"Expected 0 edges, got ${stats.totalEdges}")
  }*/
}
