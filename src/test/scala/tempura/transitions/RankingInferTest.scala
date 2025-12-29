package tempura.transitions

import tempura.helpers.Utils.failwith
import org.scalatest.funsuite.AnyFunSuite
import tempura.cozy.Transforms
import tempura.parsing.io.{PathOf, StringReader, TDLReader, VMTReader}
import tempura.parsing.printers.{DotPrinter, TDLPrinter}
import tempura.parsing.sexpr.StringToSExprParser
import tempura.smt.{SmtSolver, Z3Solver}

class RankingInferTest extends AnyFunSuite {
/*
  test("ranking_infer1.tdl") {
    val trs = TDLReader("examples/ranking_infer1.tdl") match {
      case Right(t) => t
      case Left(e) => failwith("error during parsing of TDL: " + e)
    }
    val solver = Z3Solver.Z3Solver(trs.getTypeEnv, trs.getInterpEnv)
    val solverEnv = solver.box
    solver.initialize(SmtSolver.allLia)
    println(s"Transition system assumptions: ${trs.assumptions}")
    trs.insertAssumptions(solverEnv)
    val sampledAxiom = trs.sampleTheoryModel(solverEnv).get
    println(s"sampled axiom: ${sampledAxiom}")
    solver.addTerms(List(sampledAxiom))
    println(s"transition variables: ${trs.transitionVars.mkString(",")}")
    println(TDLPrinter(trs.getTypeEnv, trs.getInterpEnv)(trs))

    val fixpointIterator = BackwardsFixpoint(trs, solver.box, List(), false)

    fixpointIterator.setMaxSteps(5000)
    fixpointIterator.run()

    val graph = fixpointIterator.getStateGraph
    println("visualizing state graph...")
    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x =>
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        None)
    graphPrinter.visualizeDOT(None, true)

  }


  test("ranking_infer1_trimmed.vmt") {
    val trs = VMTReader("examples/ranking_infer1_trimmed_2.vmt") match {
      case Right(t) => t
      case Left(e) => failwith("error during parsing of VMT: " + e)
    }
    println(trs)
    val solver = Z3Solver.Z3Solver(trs.getTypeEnv, trs.getInterpEnv)
    val solverEnv = solver.box
    solver.initialize(SmtSolver.allLia)
    println(s"Transition system assumptions: ${trs.assumptions}")
    trs.insertAssumptions(solverEnv)
    val sampledAxiom = trs.sampleTheoryModel(solverEnv).get
    println(s"sampled axiom: ${sampledAxiom}")
    solver.addTerms(List(sampledAxiom))
    println(s"transition variables: ${trs.transitionVars.mkString(",")}")
    val fixpointIterator = BackwardsFixpoint(trs, solver.box, List(), false)

    fixpointIterator.setMaxSteps(5000)
    fixpointIterator.run()

    val graph = fixpointIterator.getStateGraph
    println("visualizing state graph...")
    val graphPrinter =
      DotPrinter.Printer(graph, true,
        (x => DotPrinter.defaultNodeConfig), (e => DotPrinter.defaultEdgeConfig),
        Some(x =>
          s"${x}: ${graph.labelOf(x).toString}"
        ),
        None)
    graphPrinter.visualizeDOT(None, true)

  }
*/
}
