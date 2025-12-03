package org.abstractpredicates.transitions

class LabeledTrace[NodeLabel, EdgeLabel](graph: LabeledGraph[NodeLabel, EdgeLabel],
                                         trace: List[(graph.Vertex, EdgeLabel, graph.Vertex)]) {

  val edges: Array[(graph.Vertex, EdgeLabel, graph.Vertex)] = trace.toArray

  // TODO
}
