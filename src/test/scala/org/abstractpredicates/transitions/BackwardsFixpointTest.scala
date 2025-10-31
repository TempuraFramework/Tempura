package org.abstractpredicates.transitions

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.smt.{SmtSolver, Z3Solver}

/**
 * Test suite for BackwardsFixpoint explicit-state model checker.
 *
 * Tests cover:
 * - Simple boolean transition systems with liveness properties
 * - Bounded counter systems
 * - Co-reachability analysis (states that can reach live states)
 * - Liveness reachability checking
 */
class BackwardsFixpointTest extends AnyFunSuite {

  /**
   * Helper: Create a simple two-state boolean transition system
   *
   * State: x (boolean)
   * Init: ¬x
   * Trans: x' = ¬x (toggle)
   * LiveAssertions: x (only state where x=true is live)
   *
   * This should produce exactly 2 states: {x=false} and {x=true}
   * Backwards from x=true, we find x=false as predecessor.
   */
  def createToggleSystemWithLiveness(): (TransitionSystem, SmtSolver.SolverEnvironment) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())

    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    val init = Core.mkNot(x)
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    // Liveness: x must be true
    val liveAssertion = x

    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    (trs, solver.box)
  }

  /**
   * Helper: Create a 2-bit counter system with liveness
   *
   * States: b0, b1 (booleans representing a 2-bit counter)
   * Init: b0 = false, b1 = false (count = 0)
   * Trans: increment modulo 4
   *   next_b0 = ¬b0
   *   next_b1 = b1 XOR b0
   * LiveAssertions: b0 ∧ b1 (only state 11 is live)
   *
   * States: 00 -> 10 -> 01 -> 11 -> 00 (cycle of length 4)
   * Backwards from 11, we should find all states (since there's a cycle)
   */
  def createCounterSystemWithLiveness(): (TransitionSystem, SmtSolver.SolverEnvironment) = {
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
    val trans = Core.mkAnd(List(
      Core.mkEq(next_b0, Core.mkNot(b0)),
      Core.mkEq(next_b1,
        Core.mkOr(List(
          Core.mkAnd(List(b1, Core.mkNot(b0))),
          Core.mkAnd(List(Core.mkNot(b1), b0))
        ))
      )
    ))

    // Liveness: both bits must be true (state 11)
    val liveAssertion = Core.mkAnd(List(b0, b1))

    val trs = TransitionSystem(
      stateVars = Set(timedVar0, timedVar1),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    (trs, solver.box)
  }

  /**
   * Helper: Create a system with unreachable liveness
   *
   * States: x (boolean)
   * Init: ¬x
   * Trans: x' = x (no change)
   * LiveAssertions: x (live state is x=true)
   *
   * Since transitions preserve x, and init has x=false,
   * the live state x=true is unreachable from init.
   */
  def createUnreachableLivenessSystem(): (TransitionSystem, SmtSolver.SolverEnvironment) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())

    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    val init = Core.mkNot(x)
    val trans = Core.mkEq(next_x, x) // No change transition

    // Liveness: x must be true (unreachable from init)
    val liveAssertion = x

    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    (trs, solver.box)
  }

  /**
   * Helper: Create a mutex system with liveness
   *
   * States: p0, p1 (booleans representing processes in critical section)
   * Init: ¬p0 ∧ ¬p1
   * Trans: (p0' = ¬p0 ∧ p1' = p1) ∨ (p0' = p0 ∧ p1' = ¬p1)
   * LiveAssertions: p0 ∨ p1 (at least one process must be in critical section)
   *
   * Live states: (1,0) and (0,1)
   * Backwards exploration should find all states that can reach these.
   */
  def createMutexSystemWithLiveness(): (TransitionSystem, SolverEnvironment) = {
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

    // Liveness: at least one process must be in critical section
    val liveAssertion = Core.mkOr(List(p0, p1))

    val trs = TransitionSystem(
      stateVars = Set(timedVar0, timedVar1),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv).box

    (trs, solver)
  }

  test("toggle system: backward exploration from live states") {
    val (trs, solver) = createToggleSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(10)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    println(s"Toggle system (backwards) statistics:\n${stats}")

    // Should have exactly 2 states: x=true (live) and x=false (predecessor)
    assert(stats.totalStates == 2, s"Expected 2 states, got ${stats.totalStates}")

    // Should have 1 edge: from x=true back to x=false
    assert(stats.totalEdges == 1, s"Expected 1 edge, got ${stats.totalEdges}")
  }

  test("counter system: backward reachability") {
    val (trs, solver) = createCounterSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(20)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    println(s"Counter system (backwards) statistics:\n${stats}")

    // Should have exactly 4 states (all states can reach the live state due to cycle)
    assert(stats.totalStates == 4, s"Expected 4 states, got ${stats.totalStates}")
  }

  test("unreachable liveness: no initial states can reach live state") {
    val (trs, solver) = createUnreachableLivenessSystem()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(20)
    fixpoint.run()

    // Check if initial states can reach live states
    val livenessReachable = fixpoint.checkLivenessReachable()

    assert(!livenessReachable, "Liveness should NOT be reachable from initial states")

    val stats = fixpoint.getStatistics

    // Should have 1 live state (x=true) and possibly its predecessor
    // But x=false cannot reach x=true, so we should have only 1 state
    assert(stats.totalStates == 1, s"Expected 1 state (just live state), got ${stats.totalStates}")
  }

  test("mutex system: liveness reachable from init") {
    val (trs, solver) = createMutexSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(20)
    fixpoint.run()

    // Check if initial states can reach live states
    val livenessReachable = fixpoint.checkLivenessReachable()

    assert(livenessReachable, "Liveness should be reachable from initial states")
  }

  test("toggle system: live states computation") {
    val (trs, solver) = createToggleSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val liveStates = fixpoint.computeLiveStates()

    // Should have exactly 1 live state (x=true)
    assert(liveStates.size == 1, s"Expected 1 live state, got ${liveStates.size}")
  }

  test("counter system: live states computation") {
    val (trs, solver) = createCounterSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val liveStates = fixpoint.computeLiveStates()

    // Should have exactly 1 live state (b0=true, b1=true)
    assert(liveStates.size == 1, s"Expected 1 live state, got ${liveStates.size}")
  }

  test("mutex system: multiple live states") {
    val (trs, solver) = createMutexSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val liveStates = fixpoint.computeLiveStates()

    // Should have 2 live states: (1,0) and (0,1)
    assert(liveStates.size == 2, s"Expected 2 live states, got ${liveStates.size}")
  }

  test("toggle system: max steps limit") {
    val (trs, solver) = createToggleSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    // Set max steps to 0 - should only compute live states
    fixpoint.setMaxSteps(0)
    fixpoint.run()

    val stats = fixpoint.getStatistics
    assert(stats.totalStates == 1, s"With maxSteps=0, should have 1 state, got ${stats.totalStates}")
    assert(stats.explorationSteps == 0, s"Should have 0 exploration steps, got ${stats.explorationSteps}")
  }

  test("fair edges and ranking with fairness condition") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())
    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    val init = Core.mkTrue
    val trans = Core.mkOr(List(
      Core.mkAnd(List(Core.mkEq(x, Core.mkFalse), Core.mkEq(next_x, Core.mkTrue))),
      Core.mkAnd(List(Core.mkEq(x, Core.mkTrue), Core.mkEq(next_x, Core.mkFalse)))
    ))

    val liveAssertion = Core.mkEq(x, Core.mkTrue)
    val fairnessCondition = Core.mkEq(next_x, Core.mkTrue)

    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(fairnessCondition),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = BackwardsFixpoint(trs, solver.box, List())

    fixpoint.setMaxSteps(10)
    fixpoint.run()

    val fairEdges = fixpoint.getFairEdges
    assert(fairEdges.size == 1, s"Expected exactly one fair edge, found ${fairEdges.size}")

    val ranking = fixpoint.getRanking
    val ranks = ranking.values.toSet
    assert(ranks == Set(0, 1), s"Expected ranking set {0,1}, found ${ranks}")
  }

  test("empty liveness assertions: all states are live") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())
    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    val init = Core.mkNot(x)
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    // No liveness assertions - defaults to true (all states are live)
    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(), // Empty!
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = BackwardsFixpoint(trs, solver.box, List())

    fixpoint.setMaxSteps(10)
    fixpoint.run()

    val stats = fixpoint.getStatistics

    // With no liveness assertions (true), both states are live
    assert(stats.totalStates == 2, s"Expected 2 states, got ${stats.totalStates}")
  }

  test("theory axioms: constrained backward exploration") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())
    val timedVar = TimedVariable("x", "next_x", 0, Core.BoolSort())

    // Init: true (any value)
    val init = Core.mkTrue

    // Trans: x' = ¬x
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    // Liveness: x must be false
    val liveAssertion = Core.mkNot(x)

    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      init = init,
      trans = trans,
      assertions = List(),
      assumptions = List(),
      liveAssertions = List(liveAssertion),
      liveAssumptions = List(),
      fairness = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    // Theory axiom: x must be false
    val theoryAxiom = Core.mkNot(x)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = BackwardsFixpoint(trs, solver.box, List(theoryAxiom))

    fixpoint.setMaxSteps(10)
    fixpoint.run()

    val stats = fixpoint.getStatistics

    // With theory axiom x = false, should only find state where x = false
    // Predecessor would be x = true, but that violates theory
    // So should have 1 state with 0 predecessors
    assert(stats.totalStates == 1, s"Expected 1 state, got ${stats.totalStates}")
    assert(stats.totalEdges == 0, s"Expected 0 edges, got ${stats.totalEdges}")
  }

  test("co-reachability check: isCoReachable") {
    val (trs, solver) = createToggleSystemWithLiveness()
    val fixpoint = BackwardsFixpoint(trs, solver, List())

    fixpoint.setMaxSteps(10)
    val graph = fixpoint.run()

    val stats = fixpoint.getStatistics

    // After backward exploration, both states should be co-reachable
    // We can verify this by checking that we found 2 states
    assert(stats.totalStates == 2, "Both states should be co-reachable")

    // The graph should contain both the live state and its predecessor
    assert(graph.allNodes.size == 2, "Graph should contain 2 nodes")
  }
}
