package tempura.transitions

import org.scalatest.funsuite.AnyFunSuite
import tempura.parsing.printers.DotPrinter

import scala.collection.mutable

class LabeledGraphTest extends AnyFunSuite {

  def mkPrinter[N, E](graph: LabeledGraph[N, E]) =
    DotPrinter.Printer(graph,
      true,
      (_ => DotPrinter.defaultNodeConfig),
      (_ => DotPrinter.defaultEdgeConfig),
      None,
      None
    )

  test("forwards closed") {
    val graph = LabeledGraph(
      (0, "0", List(
        ("0-1", 1),
          ("0-2", 2),
        ("0-3", 3),
          ("0-4",4)
      )),
      (1,"1",List(
        ("1-2",2)
      )),
      (2,"2", List(
        ("2-5", 5)
      )),
      (6,"6", List(
        ("6-2", 2)
      )),
      (5, "5", List())
    )
    val printer = mkPrinter(graph)
    println(printer.dotString)
    println(s"source: ${graph.sources}")
    println(s"sink: ${graph.sinks}")
    val subgraph = graph.forwardsClosed(Set(6))
    val subgraphPrinter = mkPrinter(subgraph)
    println("subgraph: " + subgraphPrinter.dotString)
  }

  test("backwards closed") {
    val graph = LabeledGraph(
      (0, "0", List(
        ("0-1", 1),
          ("0-2", 2),
        ("0-3", 3),
          ("0-4",4)
      )),
      (1,"1",List(
        ("1-2",2)
      )),
      (2,"2", List(
        ("2-5", 5)
      )),
      (6,"6", List(
        ("6-2", 2)
      )),
      (5, "5", List())
    )
    val printer = mkPrinter(graph)
    println(printer.dotString)
    println(s"source: ${graph.sources}")
    println(s"sink: ${graph.sinks}")
    val subgraph = graph.backwardsClosed(Set(5))
    val subgraphPrinter = mkPrinter(subgraph)
    println("subgraph: " + subgraphPrinter.dotString)
  }

  test("graph utils") {
    val graph = LabeledGraph(
      (0, "0", List(
        ("0-1", 1),
        ("0-2", 2),
        ("0-3", 3)
      )),
      (1, "1", List(
        ("1-2", 2),
        ("1-3", 3)
      )),
      (3, "3", List(
        ("3-1", 1)
      )))

    val printer = mkPrinter(graph)
    println(printer.dotString)

    println("000000000000000000000000000000000")
    println("nodeList: " + graph.allNodes)
    println("edgeList: " + graph.allEdges)

    assert(graph.sources == mutable.Set(0))
    assert(graph.sinks == mutable.Set())

    println("removing edge 3-1")
    graph.removeEdge(3, 1)
    println(s"sinks: ${graph.sinks}")
    println(s"sources: ${graph.sources}")
    assert(graph.sinks == mutable.Set(3))
    assert(graph.sources == mutable.Set(0))
    //printer.visualizeDOT()
  }
}
