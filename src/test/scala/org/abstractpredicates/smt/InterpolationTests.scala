package org.abstractpredicates.smt

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.smt.SmtSolver.Result
import org.abstractpredicates.smt.interpolants.{Cvc5Interpolation, InterpolationEngine, QEInterpolation, SmtInterpolInterpolation}

class InterpolationTests extends AnyFunSuite {


  private def freshSolver() = {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    (typeEnv, interpEnv, solver)
  }

  private def itpEngines(solverEnv: SmtSolver.SolverEnvironment): List[(String, InterpolationEngine[solverEnv.LoweredTerm, solverEnv.LoweredVarDecl])] = {
    val engine0 = new SmtInterpolInterpolation(solverEnv.solver)
    engine0.initialize(SmtSolver.allLia)
    val engine1 = new Cvc5Interpolation(solverEnv.solver)
    engine1.initialize(SmtSolver.allLia)
    val engine2 = new QEInterpolation(solverEnv.solver)
    List(("SmtInterpolInterpolation", engine0), ("Cvc5Interpolation", engine1), ("QEInterpolation", engine2))
  }

  test("simple interpolation test") {
    import org.abstractpredicates.expression.Syntax.intToNumber

    val (_, interpEnv, solver) = freshSolver()

    val x = interpEnv |- ("x", Core.numericSort)
    val y = interpEnv |- ("y", Core.numericSort)
    val z = interpEnv |- ("z", Core.numericSort)

    // Assumptions for interpolation: x + y > 0 /\ x < 0
    val fmlaA0 = (x + y) > 0
    val fmlaA1 = x < 0
    val fmlaA = fmlaA0 /\ fmlaA1

    // Conjecture for interpolation: y + z > 0 \/ z < 0
    val fmlaB = Core.mkNot(((y + z) > 0) \/ (z < 0))

    itpEngines(solver.box) foreach { x =>
      val name = x._1
      val itp = x._2
      println(" ======= Testing interpolation engine " + name + " =======")
      // Call the interpolation api, while the resulting interpolant is the output
      val itpO = itp.computeInterpolant(fmlaA, fmlaB)
      println("Interpolant got: " + itpO)

      // We expect the resulting output to be a boolean formula
      assert(itpO.isDefined)
    }

  }


  test("binary interpolant exists and satisfies Craig conditions") {
    import org.abstractpredicates.expression.Syntax.intToNumber

    val (_, interpEnv, solver) = freshSolver()

    val x = interpEnv.newVar("x", Core.NumericSort())

    val a = (x >= 0) //     val a = Core.mkGe(x, Core.mkConst(0))
    val b = (x <= -1) //     val b = Core.mkLe(x, Core.mkConst(-1))

    val engines = itpEngines(solver.box)
    engines foreach {
      x =>
        val name = x._1
        val engine = x._2

        println(s" ======== Testing interpolation engine ${name} ======= ")

        val interpolantOpt = engine.computeInterpolant(a.box(), b.box())
        assert(interpolantOpt.isDefined, "Expected an interpolant for inconsistent pair")
        val interpolant: Core.Expr[Core.BoolSort] = interpolantOpt.get
        println("Interpolant got: " + interpolant)
        solver.push()
        solver.add(List(a, Core.mkNot(interpolant)))
        assert(solver.checkSat() == Result.UNSAT, "Interpolant must be implied by A")
        solver.pop()

        solver.push()
        solver.add(List(interpolant, b))
        assert(solver.checkSat() == Result.UNSAT, "Interpolant must conflict with B")
        solver.pop()
    }
  }

  test("interpolant is absent when formulas are consistent") {
    val (_, interpEnv, solver) = freshSolver()

    val x = interpEnv.newVar("x", Core.NumericSort())

    val a = Core.mkGe(x, Core.mkConst(0))
    val b = Core.mkLe(x, Core.mkConst(0))

    val engine = new SmtInterpolInterpolation(solver)
    engine.initialize(SmtSolver.allLia)

    val interpolantOpt = engine.computeInterpolant(a.box(), b.box())

    assert(interpolantOpt.isEmpty, "No interpolant should be produced for satisfiable conjunction")
  }

  test("sequence interpolants respect prefix and suffix constraints") {
    val (_, interpEnv, solver) = freshSolver()

    val x = interpEnv.newVar("x", Core.NumericSort())

    val a1 = Core.mkGe(x, Core.mkConst(0))
    val a2 = Core.mkLe(x, Core.mkConst(5))
    val a3 = Core.mkGe(x, Core.mkConst(10))

    val engine = new SmtInterpolInterpolation(solver)
    engine.initialize(SmtSolver.allLia)
    val itpsOpt = engine.computeSequenceInterpolant(List(a1.box(), a2.box(), a3.box()))

    assert(itpsOpt.isDefined, "Expected interpolant sequence for inconsistent partition")
    val interpolants = itpsOpt.get
    assert(interpolants.length == 2, s"Expected two interpolants, found ${interpolants.length}")

    val prefixes = List(List(a1), List(a1, a2))
    val suffixes = List(List(a2, a3), List(a3))

    println("Interpolants got: ")
    interpolants.zipWithIndex.foreach((x, i) => println(s"interpolant ${i}: ${x.toString}"))

    interpolants.zip(prefixes.zip(suffixes)).foreach { case (itpBox, (pref, suff)) =>
      val itp: Core.Expr[Core.BoolSort] = itpBox

      solver.push()
      solver.add(pref.map(x => x.box()))
      solver.add(List(Core.mkNot(itp)))
      assert(solver.checkSat() == Result.UNSAT, "Prefix must imply interpolant")
      solver.pop()

      solver.push()
      solver.add(itp.box() :: suff.map(x => x.box()))
      assert(solver.checkSat() == Result.UNSAT, "Interpolant must contradict suffix")
      solver.pop()
    }
  }
}
