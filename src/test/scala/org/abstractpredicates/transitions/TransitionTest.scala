package org.abstractpredicates.transitions

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.parsing.io.TransitionSystemReader
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.smt.Z3Solver
import org.abstractpredicates.transitions.TransitionFormula.{Peeled, Peeler}

class TransitionTest extends AnyFunSuite {

  private val typeEnv = Core.emptyTypeEnv
  private val interpEnv = Core.emptyInterpEnv
  private val solverEnv = Z3Solver.Z3Solver(typeEnv, interpEnv).box
  private val solver = solverEnv.solver

  test("peeler test 0") {
    val w = interpEnv.newVar("w", Core.BoolSort())
    val y = interpEnv.newVar("y", Core.BoolSort())
    val z = interpEnv.newVar("z", Core.BoolSort())
    val f0 = Core.mkImplies(w, Core.mkOr(List(y, z)))
    val peeled_f0 = Peeler(solverEnv)(f0)
    assert(peeled_f0 == Peeled.Implicative(List(), List(
      Peeled.Branch(w,
        Peeled.Disjunctive(List(Peeled.Term(y), Peeled.Term(z)))))))
    val peeled_f0_normalized = Core.mkOr(peeled_f0.normalize)
    assert(peeled_f0_normalized == Core.mkOr(List(
      Core.mkNot(w),
      Core.mkAnd(List(w, y)),
      Core.mkAnd(List(w, z))
    )))
    // val equality = Core.mkNot(Core.mkAnd(List(
    //   Core.mkImplies(f0, peeled_f0_normalized), Core.mkImplies(peeled_f0_normalized, f0))))
    val equality =
      Core.mkOr(List(
        Core.mkAnd(List(peeled_f0_normalized, Core.mkNot(f0))),
        Core.mkAnd(List(f0, Core.mkNot(peeled_f0_normalized)))
      ))
    solver.add(List(equality))

    assert(solver.checkSat() == Result.UNSAT)
  }

  test("peeler test 1") {
    val x = interpEnv.newVar("x", Core.BoolSort())
    val y = interpEnv.newVar("y", Core.BoolSort())
    val z = interpEnv.newVar("z", Core.BoolSort())
    val w = interpEnv.newVar("w", Core.BoolSort())

    val f1 = Core.mkAnd(List(
      x,
      Core.mkNot(Core.mkAnd(List(w, z))),
      Core.mkOr(List(w, z)),
      Core.mkImplies(w,
        Core.mkOr(List(y, z))
      ),
      Core.mkImplies(z,
        Core.mkOr(List(w, y))
      )
    ))

    val peeled_f1 = Peeler(solverEnv)(f1)

    assert(peeled_f1 == Peeled.Implicative(
      List(x, Core.mkNot(Core.mkAnd(List(w, z))), Core.mkOr(List(w, z))),
      List(
        Peeled.Branch(w,
          Peeled.Disjunctive(
            List(Peeled.Term(y), Peeled.Term(z))
          )),
        Peeled.Branch(z,
          Peeled.Disjunctive(
            List(Peeled.Term(w), Peeled.Term(y)))
        ))))

    val peeled_f1_normalized = Core.mkOr(peeled_f1.normalize)

    println(s"normalized formula: ${peeled_f1_normalized}")

    val equality = Core.mkOr(List(
      Core.mkAnd(List(peeled_f1_normalized, Core.mkNot(f1))),
      Core.mkAnd(List(f1, Core.mkNot(peeled_f1_normalized)))))
    solver.add(List(equality))
    solver.checkSat() match {
      case Result.SAT =>
        println("error: returned SAT")
        println(s"getModel: ${solver.getModel.get}")
        assert(false)
      case Result.UNSAT =>
        assert(true)
      case Result.UNKNOWN =>
        println("Error: Solver returned UNKNOWN")
        assert(false)
    }
  }

  test("VMT file test for peeler") {
    val reader = TransitionSystemReader("examples/ranking_infer1.vmt")
    reader.readVMT match {
      case Right(pts) =>
        println("successfully read VMT input: " + pts.toString)
        assert(true)
        val (te, ie) = (pts.getTypeEnv, pts.getInterpEnv)
        val solver = Z3Solver.Z3Solver(te, ie)
        val transition = pts.getTrans.get
        val normalizedTr = Peeler(solver.box)(transition).normalize
        println(s"Transition formula \n ${transition} \n -----\n")
        println(s"Normalized transition formula \n ${normalizedTr} \n -----\n")
        assert(true)
      case Left(error) =>
        println(s"got error: ${error}")
        assert(false)
    }
  }
}
