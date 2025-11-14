package org.abstractpredicates.transitions

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.boolSort
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.helpers.{DotPrinter, FormulaPrinter}
import org.abstractpredicates.helpers.Utils.unexpected
import org.abstractpredicates.smt.SmtSolver.Result
import org.abstractpredicates.smt.{SmtSolver, Z3Solver}

import scala.language.postfixOps

class MyFixpointTest extends AnyFunSuite {

  private def formTheoryAxioms(typeEnv: Core.TypeEnv,
                               interpEnv: Core.InterpEnv,
                               solver: SmtSolver.SolverEnvironment,
                               ltDef: Core.Expr[Core.FunSort[Core.BoolSort]],
                               zero: Core.Expr[Core.FiniteUniverseSort],
                               succ: Core.Expr[Core.FunSort[Core.BoolSort]],
                               timeSort: Core.FiniteUniverseSort) = {


    val ltSort = Core.funSort(List(timeSort.box, timeSort.box), Core.BoolSort())
    val succTimeSort = Core.FunSort(List(timeSort.box, timeSort.box), Core.BoolSort())

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

    def succApply(lhs: Core.Expr[Core.FiniteUniverseSort], rhs: Core.Expr[Core.FiniteUniverseSort]): Core.Expr[Core.BoolSort] =
      app(succ, lhs, rhs)

    val immediateSuccessor =
      Core.mkForall(
        vars("X", "Y", "Z"),
        Core.mkNot(succApply(v("X"), v("Z"))) \/
          (lt(v("X"), v("Z")) /\ Core.mkNot(lt(v("X"), v("Y")) /\ lt(v("Y"), v("Z"))))
      )

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
      ("zero", timeSort)
    )

    solver().checkSat() match {
      case Result.SAT =>
        val model = solver().getModel.get
        solver().pop()
        val axiom = model.asTerm(vocab)
        List(axiom)
      case _ =>
        solver().pop()
        unexpected("")
    }
  }

  test("my test 1") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val cardinality = 3

    val timeSort = typeEnv |- Core.finiteSort("time", cardinality)
    val succTimeSort = Core.FunSort(List(timeSort.box, timeSort.box), Core.BoolSort())

    val ltSort = Core.funSort(List(timeSort.box, timeSort.box), Core.BoolSort())
    val succ = interpEnv |- ("succ", succTimeSort)

    val ltDef = interpEnv |- ("lessThan", ltSort)
    val zero = interpEnv |- ("zero", timeSort)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)

    val axioms = formTheoryAxioms(typeEnv, interpEnv, solver.box, ltDef, zero, succ, timeSort)
    solver.push()


    val counter0Def = interpEnv |- ("cnt0", timeSort)
    val counter1Def = interpEnv |- ("cnt1", timeSort)
    val flagDef = interpEnv |- ("flag", Core.boolSort)

    val counter0NextStateDef = interpEnv |- ("cnt0_next", timeSort)
    val counter1NextStateDef = interpEnv |- ("cnt1_next", timeSort)
    val flagNextStateDef = interpEnv |- ("flag_next", Core.boolSort)

    val counter0 = TimedVariable("cnt0", "cnt0_next", 0, timeSort)
    val counter1 = TimedVariable("cnt1", "cnt1_next", 0, timeSort)
    val flag = TimedVariable("flag", "flag_next", 0, Core.boolSort)

    val queueSort = Core.arraySort(timeSort, Core.boolSort)
    val queueDef = interpEnv |- ("queue", queueSort)
    val queue = TimedVariable("queue", "queue_next", 0, queueSort)

    val stateVars = Set(counter0, counter1, flag)

    val initCond = Core.mkForall(List(("x", timeSort)),
      Core.mkEq(queueDef @<Core.mkVar("x", timeSort)>, Core.mkFalse))
      /\ Core.mkEq(counter0Def, zero)
      /\ Core.mkNot(Core.mkEq(counter1Def, counter0Def))

    val transCond = {
      Core.mkEq(queueDef @< counter0Def >, Core.mkTrue) /\
      Core.mkExists(List(("x", timeSort)),
        succ(("arg0", Core.mkVar("x", timeSort)), ("arg1", counter0Def))
          |=
          Core.mkEq(counter0NextStateDef, Core.mkVar("x", timeSort))
      ) /\
        Core.mkNot(Core.mkEq(counter1NextStateDef, counter1Def))
    }

    val liveAssertion =
      List(
        Core.mkForall(List(("x", timeSort)), queueDef @<Core.mkVar("x", timeSort)>)
      )
    val fairness = List(Core.mkTrue)

    val ts = TransitionSystem(
      stateVars,
      initCond,
      transCond,
      List(), // assertions for safety properties
      List(),
      liveAssertion, // liveness assertion
      List(), // liveness assumption
      fairness,
      typeEnv,
      interpEnv
    )

    ts.insertAssumptions(solver.box)
    ts.insertLivenessAssumptions(solver.box)

    val fixpointIterator = BackwardsFixpoint(ts, solver.box, axioms, false)

    fixpointIterator.setMaxSteps(1000)
    fixpointIterator.run()

    val graph = fixpointIterator.getStateGraph
    println("visualizing state graph...")
    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x => 
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        Some(e =>
          s"${FormulaPrinter.ExprPrinter(graph.labelOf(e._1, e._3).getOrElse(Core.mkTrue))()}"
        ))
    graphPrinter.visualizeDOT(None, true)
  }

}
