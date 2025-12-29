package tempura.transitions

import org.scalatest.funsuite.AnyFunSuite
import tempura.helpers.Utils.*
import tempura.expression.Syntax.*
import tempura.smt.SmtSolver.*
import tempura.expression.Syntax.*
import tempura.abstraction.PredicateAbstractionDomain
import tempura.expression.Core
import tempura.liveness.IndexTermMiner
import tempura.parsing.printers.DotPrinter.{EdgeConfig, EdgeStyles}
import tempura.parsing.printers.{DotPrinter, FormulaPrinter, TDLPrinter}
import tempura.smt.{SmtSolver, Z3Solver}

import scala.language.postfixOps


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
  def createToggleSystem(): (TransitionSystem, SmtSolver.SolverEnvironment) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv.newVar("x", Core.BoolSort())
    val next_x = interpEnv.newVar("next_x", Core.BoolSort())

    val timedVar = StateVariable("x", "next_x", Core.BoolSort())

    val init = Core.mkNot(x)
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans)), Set(timedVar), Set())

    val trs = TransitionSystem(
      init = init,
      trans = transition,
      properties = List(),
      assumptions = List(),
      liveProperties = List(),
      liveAssumptions = List(),
      fairAssumptions = List(),
      theoryAxioms = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    (trs, solver.box)
  }

  /**
   * Helper: Create a 2-bit counter system
   *
   * States: b0, b1 (booleans representing a 2-bit counter)
   * Init: b0 = false, b1 = false (count = 0)
   * Trans: increment modulo 4
   * next_b0 = ¬b0
   * next_b1 = b1 XOR b0
   *
   * States: 00 -> 10 -> 01 -> 11 -> 00 (cycle of length 4)
   */
  def createCounterSystem(): (TransitionSystem, SmtSolver.SolverEnvironment) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val b0 = interpEnv |- ("b0", Core.BoolSort())
    val b1 = interpEnv |- ("b1", Core.BoolSort())
    val next_b0 = interpEnv |- ("next_b0", Core.BoolSort())
    val next_b1 = interpEnv |- ("next_b1", Core.BoolSort())

    val timedVar0 = StateVariable("b0", "next_b0", Core.BoolSort())
    val timedVar1 = StateVariable("b1", "next_b1", Core.BoolSort())

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

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans)), Set(timedVar0, timedVar1), Set())

    val trs = TransitionSystem(
      init = init,
      trans = transition,
      properties = List(),
      assumptions = List(),
      liveProperties = List(),
      liveAssumptions = List(),
      fairAssumptions = List(),
      theoryAxioms = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)

    (trs, solver.box)
  }

  /**
   * Helper: Create a simple mutex system
   *
   * States: p0, p1 (booleans representing processes in critical section)
   * Init: ¬p0 ∧ ¬p1
   * Trans: (p0' = ¬p0 ∧ p1' = p1) ∨ (p0' = p0 ∧ p1' = ¬p1)
   * (one process enters/leaves at a time)
   *
   * XXX: (1,1) is reachable -RF 12/9/25.
   */
  def createMutexSystem(): (TransitionSystem, SolverEnvironment, Core.Expr[Core.BoolSort]) = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val p0 = interpEnv.newVar("p0", Core.BoolSort())
    val p1 = interpEnv.newVar("p1", Core.BoolSort())
    val next_p0 = interpEnv.newVar("next_p0", Core.BoolSort())
    val next_p1 = interpEnv.newVar("next_p1", Core.BoolSort())

    val timedVar0 = StateVariable("p0", "next_p0", Core.BoolSort())
    val timedVar1 = StateVariable("p1", "next_p1", Core.BoolSort())

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

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans)), Set(timedVar0, timedVar1), Set())

    val trs = TransitionSystem(
      init = init,
      trans = transition,
      properties = List(),
      assumptions = List(),
      liveProperties = List(),
      liveAssumptions = List(),
      fairAssumptions = List(),
      theoryAxioms = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv).box

    // Mutual exclusion property: ¬(p0 ∧ p1)
    val mutexProperty = Core.mkNot(Core.mkAnd(List(p0, p1)))

    (trs, solver, mutexProperty)
  }

  test("toggle system") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())
    println("running toggle system...")
    val graph = fixpoint.reachableStates()

    println(s"Toggle system reachable states computation done")

    // Should have exactly 2 states
    //assert(stats.totalStates == 2, s"Expected 2 states, got ${stats.totalStates}")

    // Should have 2 edges (forming a cycle)
    //assert(stats.totalEdges == 2, s"Expected 2 edges, got ${stats.totalEdges}")
    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x =>
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        Some(e =>
          s"${(graph.labelOf(e._1, e._3).get)}"
        ))

    graphPrinter.visualizeDOT(None, true)

  }

  test("counter system") {
    val (trs, solver) = createCounterSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    val graph = fixpoint.reachableStates()

    //val stats = fixpoint.getStatistics

    //println(s"Counter system statistics:\n${stats}")

    // Should have exactly 4 states (2-bit counter: 00, 01, 10, 11)
    // assert(stats.totalStates == 4, s"Expected 4 states, got ${stats.totalStates}")

    // Should have 4 edges (forming a cycle)
    // assert(stats.totalEdges == 4, s"Expected 4 edges, got ${stats.totalEdges}")

    // val graph0 = fixpoint.getStateGraph
    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x =>
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        Some(e =>
          s"${graph.labelOf(e._1, e._3).get}"
        ))

    graphPrinter.visualizeDOT(None, true)

    // Should have exactly 4 states (all states can reach the live state due to cycle)
    // assert(stats.totalStates == 4, s"Expected 4 states, got ${stats.totalStates}")

  }

  test("mutex system") {
    val (trs, solver, _) = createMutexSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    val graph = fixpoint.reachableStates()

    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x =>
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        Some(e =>
          s"${graph.labelOf(e._1, e._3).get}"
        ))

    graphPrinter.visualizeDOT(None, true)


    // XXX: The following is wrong. (1,1) is reachable. -RF 12/9/25
    // Should have exactly 3 states: (0,0), (1,0), (0,1)
    // State (1,1) is unreachable due to mutual exclusion
    //assert(stats.totalStates == 3, s"Expected 3 states, got ${stats.totalStates}")
  }


  test("finite-liveness") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val cardinality = 4

    // The finite sort
    val timeSort = typeEnv |- Core.finiteSort("time", cardinality)

    // State-holding variables
    val counter = interpEnv |- ("counter", timeSort)
    val counterNext = interpEnv |- ("counter_next", timeSort)
    val counterStateVar = StateVariable("counter", "counter_next", timeSort)

    val arr = interpEnv |- ("arr", Core.arraySort(timeSort, Core.boolSort))
    val arrNext = interpEnv |- ("arr_next", Core.arraySort(timeSort, Core.boolSort))
    val arrStateVar = StateVariable("arr", "arr_next", Core.arraySort(timeSort, Core.boolSort))

    val fairFlagHist = interpEnv |- ("fairFlagH", Core.BoolSort())
    val fairFlagHistNext = interpEnv |- ("fairFlagH_next", Core.BoolSort())
    val fairFlagHistStateVar = StateVariable("fairFlagH", "fairFlagH_next", Core.BoolSort())

    // Transition variables
    val fairFlag = interpEnv |- ("_fairFlag", Core.BoolSort())
    val x = interpEnv |- ("_x", timeSort)

    val counterVar = StateVariable("counter", "counter_next", timeSort)
    val arrVar = StateVariable("arr", "arr_next", Core.arraySort(timeSort, Core.boolSort))

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    //
    // Initialization condition: all of arr is false, and counter = 0, and fairFlag = 0
    //   forall x: time. arr[x] = False
    //    /\ counter = 0
    val init = Core.mkForall(List(("x", timeSort)),
      Core.mkEq(arr @< Core.mkVar("x", timeSort) >, Core.mkFalse)
    )
      /\ Core.mkEq(counter, Core.Const(Core.SortValue.FiniteUniverseValue(0, timeSort)))
      /\ Core.mkEq(fairFlagHist, Core.mkFalse)


    // Transition condition:
    //  exists x: time.
    //    arr[x]=false => arr' = store(arr, x, true) /\ counter' = x
    //  \/ (arr' = arr /\ counter' = counter)
    val trans0 =
      fairFlag /\ (
        (Core.mkEq(arr @< x >, Core.mkFalse)
          /\ (
          Core.mkEq(arrNext, arr @< x >= Core.mkTrue) /\ Core.mkEq(counterNext, x)
          ))
        ) /\ Core.mkEq(fairFlagHistNext, fairFlag)

    // frame condition on state vars
    val trans1 = Core.mkNot(fairFlag) /\ (Core.mkEq(arrNext, arr) /\ Core.mkEq(counterNext, counter)) /\ Core.mkEq(fairFlagHistNext, fairFlag)

    val stateVars = Set(counterStateVar, arrStateVar, fairFlagHistStateVar)
    val transVars: Set[(String, Core.BoxedSort)] = Set(("_fairFlag", Core.boolSort), ("_x", timeSort))

    val live0 = Core.mkForall(List(("x", timeSort)), Core.mkEq(arr @< Core.mkVar("x", timeSort) >, Core.mkTrue))
    val liveAssertion =
      List(("live0",
        live0
      ))
    val fairness = List(("fair0", fairFlagHist)) // TODO TODO here

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans0), ("trans1", trans1)), stateVars, transVars)

    val ts = TransitionSystem(
      init,
      transition,
      List(), // assertions for safety properties
      List(),
      liveAssertion, // liveness assertion
      List(), // liveness assumption
      fairness,
      List(),
      typeEnv,
      interpEnv
    )
    ts.insertAssumptions(solver.box)

    val fix = ForwardsFixpoint(ts, solver.box, List())

    val graph1 = fix.reachableStates()
    // val graph2 = fix.liveStates(graph1)

    println("getting index term...")
    val fn = IndexTermMiner.apply(Tuple3(solver.box, ts, graph1))
    println(s"index term result: ${fn.toString}")

    println("visualizing state graph...")
    val graphPrinter =
      DotPrinter.Printer(graph1, true, States.stateGraphNodeConfig(ts, graph1),
        e =>
          val fair = Core.mkVar("_fairFlag", Core.BoolSort())
          if e._2.isFair(fair) then {
            DotPrinter.EdgeConfig("red", DotPrinter.EdgeStyles.Dashed)
          } else {
            DotPrinter.defaultEdgeConfig
          }
        ,
        Some(x =>
          s"${x}: ${graph1.labelOf(x).toString}"
        ),
        Some(e =>
          e._2.toString
        ))
    graphPrinter.visualizeDOT(None, true)

    println("-------------------------------------")
    println(TDLPrinter(typeEnv, interpEnv)(ts).toString)

  }

  // samples a theory model for linear orders on `timeSort`
  // returns a list of axioms for the theory model sampled
  private def formTheoryModel(typeEnv: Core.TypeEnv,
                               interpEnv: Core.InterpEnv,
                               solver: SmtSolver.SolverEnvironment,
                               ltDef: Core.Expr[Core.FunSort[Core.BoolSort]],
                               zero: Core.Expr[Core.FiniteUniverseSort],
                               timeSort: Core.FiniteUniverseSort) = {


    val ltSort = Core.funSort(List(timeSort.box, timeSort.box), Core.BoolSort())

    def app(fun: Core.Expr[Core.FunSort[Core.BoolSort]],
            args: Core.Expr[Core.FiniteUniverseSort]*): Core.Expr[Core.BoolSort] =
      val bindings = args.zipWithIndex.map { case (arg, idx) => (s"arg_$idx", arg.box()) }.toList
      Core.mkSubst("app", bindings, fun)

    def lt(lhs: Core.Expr[Core.FiniteUniverseSort], rhs: Core.Expr[Core.FiniteUniverseSort]): Core.Expr[Core.BoolSort] =
      app(ltDef, lhs, rhs)

    def vars(names: String*): List[(String, Core.BoxedSort)] =
      names.toList.map(name => (name, timeSort.box))

    def v(name: String): Core.Expr[Core.FiniteUniverseSort] =
      Core.mkVar(name, timeSort)

    // forall T, U, V.
    //  either not(T < U /\ U < V) or T < V
    val transitiveOrder =
      Core.mkForall(
        vars("T", "U", "V"),
        Core.mkNot(lt(v("T"), v("U")) /\ lt(v("U"), v("V"))) \/ lt(v("T"), v("V"))
      )

    val antisymmetric =
      Core.mkForall(
        List(("T", timeSort), ("U", timeSort)),
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

    solver().push()
    solver().add(List(transitiveOrder, antisymmetric, totalOrder, zeroLeast))

    val vocab: Set[(String, Core.BoxedSort)] = Set(
      ("lessThan", ltSort),
      ("zero", timeSort),
    )

    solver().checkSat() match {
      case Result.SAT =>
        val model = solver().getModel.get
        solver().pop()
        val axiom = ("ax0", model.formula(vocab))
        List(axiom)
      case _ =>
        solver().pop()
        unexpected("")
    }
  }


  // Pick an element e that is special,
  // a state is live if all elements less than e is set to true in the `arr` array
  test("liveness1") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val cardinality = 3

    // The finite sort
    val timeSort = typeEnv |- Core.finiteSort("time", cardinality)


    // State-holding variables
    val counter = interpEnv |- ("counter", timeSort)
    val counterNext = interpEnv |- ("counter_next", timeSort)
    val counterStateVar = StateVariable("counter", "counter_next", timeSort)

    val arr = interpEnv |- ("arr", Core.arraySort(timeSort, Core.boolSort))
    val arrNext = interpEnv |- ("arr_next", Core.arraySort(timeSort, Core.boolSort))
    val arrStateVar = StateVariable("arr", "arr_next", Core.arraySort(timeSort, Core.boolSort))

    val fairFlagHist = interpEnv |- ("fairFlagH", Core.BoolSort())
    val fairFlagHistNext = interpEnv |- ("fairFlagH_next", Core.BoolSort())
    val fairFlagHistStateVar = StateVariable("fairFlagH", "fairFlagH_next", Core.BoolSort())

    val e = interpEnv |- ("e", timeSort)
    val eNext = interpEnv |- ("e_next", timeSort)
    val eStateVar = StateVariable("e", "e_next", timeSort)

    val counterVar = StateVariable("counter", "counter_next", timeSort)
    val arrVar = StateVariable("arr", "arr_next", Core.arraySort(timeSort, Core.boolSort))

    // Transition variables
    val fairFlag = interpEnv |- ("_fairFlag", Core.BoolSort())
    val x = interpEnv |- ("_x", timeSort)


    // theory vars
    val ltSort = Core.funSort(List(timeSort.box, timeSort.box), Core.BoolSort())

    val ltDef = interpEnv |- ("lessThan", ltSort)
    val zero = interpEnv |- ("zero", timeSort)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val theoryAxioms = formTheoryModel(typeEnv, interpEnv, solver.box, ltDef, zero, timeSort)



    //
    // Initialization condition: all of arr is false, and counter = 0, and fairFlag = 0
    //   forall x: time. arr[x] = False
    //    /\ counter = 0
    val init = Core.mkForall(List(("x", timeSort)),
      Core.mkEq(arr @< Core.mkVar("x", timeSort) >, Core.mkFalse)
    )
      /\ Core.mkEq(counter, Core.Const(Core.SortValue.FiniteUniverseValue(0, timeSort)))
      /\ Core.mkEq(fairFlagHist, Core.mkFalse)


    // Transition condition:
    //  exists x: time.
    //    arr[x]=false => arr' = store(arr, x, true) /\ counter' = x
    //  \/ (arr' = arr /\ counter' = counter)
    val trans0 =
      fairFlag /\ (
        (Core.mkEq(arr @< x >, Core.mkFalse)
          /\ (
          Core.mkEq(arrNext, arr @< x >= Core.mkTrue) /\ Core.mkEq(counterNext, x)
          ))
        ) /\ Core.mkEq(fairFlagHistNext, fairFlag)

    // frame condition on state vars
    val trans1 = Core.mkNot(fairFlag) /\ (Core.mkEq(arrNext, arr) /\ Core.mkEq(counterNext, counter)) /\ Core.mkEq(fairFlagHistNext, fairFlag)

    val stateVars = Set(counterStateVar, arrStateVar, fairFlagHistStateVar, eStateVar)
    val transVars: Set[(String, Core.BoxedSort)] = Set(("_fairFlag", Core.boolSort), ("_x", timeSort))

    val live0 = Core.mkForall(List(("x", timeSort)),

      Core.mkApp(List(("arg0", Core.mkVar("x", timeSort)), ("arg1", Core.mkVar("e", timeSort))), ltDef)
        |=
      Core.mkEq(arr @< Core.mkVar("x", timeSort) >,

        Core.mkTrue))
    val liveAssertion =
      List(("live0",
        live0
      ))
    val fairness = List(("fair0", fairFlagHist)) // TODO TODO here

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans0), ("trans1", trans1)), stateVars, transVars)

    val ts = TransitionSystem(
      init,
      transition,
      List(), // assertions for safety properties
      List(),
      liveAssertion, // liveness assertion
      List(), // liveness assumption
      fairness,
      theoryAxioms,
      typeEnv,
      interpEnv
    )
    ts.insertAssumptions(solver.box)

    val fix = ForwardsFixpoint(ts, solver.box, List())

    val graph1 = fix.reachableStates()
    // val graph2 = fix.liveStates(graph1)

    println("getting index term...")
    val fn = IndexTermMiner.apply(Tuple3(solver.box, ts, graph1))
    println(s"index term result: ${fn.toString}")

    //
    //(states: Set[State],
    //                                                    theoryAxioms: List[Core.Expr[Core.BoolSort]],
    //                                                    ips: List[IndexedTemplate],
    //                                                    vocabulary: Set[(String, Core.BoxedSort)],
    //                                                    indexVariables: Set[(String, Core.BoxedSort)])
    val predicatesGenerator = PredicateAbstractionDomain.IndexedPredicates(ts)
    val indexScheme : Set[(Core.BoxedSort, Int)] = Set((timeSort.box, 2), (Core.BoolSort().box, 1))
    val indexVars = predicatesGenerator.getIndexVariables(indexScheme)
    println("INDEX VARS: " + indexVars)
    println("PREDICATES: \n" + predicatesGenerator.atomicPredicates(indexVars).mkString("\n"))
    
    //  PredicateAbstractionDomain.ExistentialIndexedPredicateAbstraction(typeEnv, interpEnv)(theoryAxioms.map(x => x._2), )
    
    /*println("visualizing state graph...")
    val graphPrinter =
      DotPrinter.Printer(graph1, true, States.stateGraphNodeConfig(ts, graph1),
        e =>
          val fair = Core.mkVar("_fairFlag", Core.BoolSort())
          if e._2.isFair(fair) then {
            DotPrinter.EdgeConfig("red", DotPrinter.EdgeStyles.Dashed)
          } else {
            DotPrinter.defaultEdgeConfig
          }
        ,
        Some(x =>
          s"${x}: ${graph1.labelOf(x).toString}"
        ),
        Some(e =>
          e._2.toString
        ))
    graphPrinter.visualizeDOT(None, true)

    println("-------------------------------------")
    println(TDLPrinter(typeEnv, interpEnv)(ts).toString)*/

  }


  /*test("toggle system: initial states computation") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.initialStates()

    // Should have exactly 1 initial state
    assert(initStates.size == 1, s"Expected 1 initial state, got ${initStates.size}")
  }

  test("counter system: initial states computation") {
    val (trs, solver) = createCounterSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.initialStates()

    // Should have exactly 1 initial state (00)
    assert(initStates.size == 1, s"Expected 1 initial state, got ${initStates.size}")
  }

  test("toggle system: step-by-step exploration") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

    fixpoint.initialize()
    val initStates = fixpoint.initialStates()

    assert(initStates.size == 1, "Should have 1 initial state")

    // Explore should find the second state
    fixpoint.setMaxSteps(5)
    fixpoint.explore()

    val stats = fixpoint.getStatistics
    assert(stats.totalStates == 2, s"After exploration, should have 2 states, got ${stats.totalStates}")
  }

  test("toggle system: max steps limit") {
    val (trs, solver) = createToggleSystem()
    val fixpoint = ForwardsFixpoint(trs, solver, List())

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
    val timedVar = StateVariable("x", "next_x", 0, Core.BoolSort())

    // Unsatisfiable initial condition
    val init = Core.mkAnd(List(x, Core.mkNot(x)))
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val trs = TransitionSystem(
      stateVars = Set(timedVar),
      transitionVars = Set(),
      init = init,
      trans = List(("trans0",trans)),
      properties = List(),
      assumptions = List(),
      liveProperties = List(),
      liveAssumptions = List(),
      fairAssumptions = List(),
      theoryAxioms = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = ForwardsFixpoint(trs, solver.box, List())

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
    val timedVar = StateVariable("x", "next_x", Core.BoolSort())

    // Init: true (any value)
    val init = Core.mkTrue

    // Trans: x' = ¬x
    val trans = Core.mkEq(next_x, Core.mkNot(x))

    val transition = TransitionFormula.Transition(interpEnv, typeEnv, List(("trans0", trans)), Set(timedVar), Set())

    val trs = TransitionSystem(
      init = init,
      trans = transition,
      properties = List(),
      assumptions = List(),
      liveProperties = List(),
      liveAssumptions = List(),
      fairAssumptions = List(),
      theoryAxioms = List(),
      typeEnv = typeEnv,
      interpEnv = interpEnv
    )

    // Theory axiom: x must be false
    val theoryAxiom = Core.mkNot(x)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    val fixpoint = ForwardsFixpoint(trs, solver.box, List(theoryAxiom))

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
