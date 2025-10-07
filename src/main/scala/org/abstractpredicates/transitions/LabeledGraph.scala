package org.abstractpredicates.transitions

import scala.collection.mutable.Map as MM
import scala.collection.mutable.Set as MS
import scala.collection.immutable.Map as IM
import scala.collection.immutable.Set as IS

import cats.implicits.*

class LabeledGraph[NodeLabel, EdgeLabel] {

  type Vertex = Int 
  
  private var numNodes = 0
  private var numEdges = 0

  private val nodeLabel : MM[Vertex, NodeLabel] = MM()
  private val edgeLabel : MM[(Vertex, Vertex), EdgeLabel] = MM()
  private val nodeList : MM[Vertex, MS[Vertex]] = MM()
  private val reverseNodeList : MM[Vertex, MS[Vertex]] = MM()
  private val edgeList : MS[(Vertex, EdgeLabel, Vertex)] = MS()

  private val sourceNodes: MS[Vertex] = MS()
  private val sinkNodes: MS[Vertex] = MS()

  def addNode(label: NodeLabel): Vertex = {
    nodeLabel.update(numNodes, label)
    nodeList.update(numNodes, MS())
    reverseNodeList.update(numNodes, MS())
    sinkNodes += numNodes
    sourceNodes += numNodes
    numNodes += 1
    numNodes - 1
  }

  def addEdge(from: Vertex, to: Vertex, label: EdgeLabel): Option[(Vertex, EdgeLabel, Vertex)] = {
    (nodeLabel.get(from), nodeLabel.get(to)).tupled match {
      case Some(_, _) =>
        if sourceNodes.contains(to) then sourceNodes.remove(to)
        if sinkNodes.contains(from) then sinkNodes.remove(from)
        nodeList.update(from, nodeList.getOrElse(from, MS()) + to)
        reverseNodeList.update(to, reverseNodeList.getOrElse(to, MS()) + from)
        edgeList += ((from, label, to))
        edgeLabel.update((from, to), label)
        Some(from, label, to)
      case None => None
    }
  }

  def removeNode(node: Vertex): Unit = {
    nodeList.get(node) match {
      case Some(successors) =>
        successors.foreach(nextNode =>
          val weight = edgeLabel((node, nextNode))
          edgeList.remove((node, weight, nextNode))
          edgeLabel.remove((node, nextNode))
          reverseNodeList.update(nextNode, reverseNodeList(nextNode) - node)
          if reverseNodeList(nextNode).isEmpty then sinkNodes += nextNode
        )
        nodeList.remove(node)
        reverseNodeList.remove(node)
      case None => ()
    }
  }

  def removeEdge(from: Vertex, to: Vertex): Unit = {
    nodeList.get(from) match {
      case Some(fromSucc) =>
        nodeList.update(from, fromSucc - to)
      case None => ()
    }
    reverseNodeList.get(to) match {
      case Some(toPred) =>
        reverseNodeList.update(to, toPred - from)
      case None => ()
    }
    val weight = edgeLabel((from, to))
    edgeList.remove((from, weight, to))
    edgeLabel.remove((from, to))
    if nodeList(from).isEmpty then sourceNodes += from
    if reverseNodeList(to).isEmpty then sinkNodes += to
  }

  def labelOf(node: Vertex) : Option[NodeLabel] = nodeLabel.get(node)
  def labelOf(from: Vertex, to: Vertex): Option[EdgeLabel] = edgeLabel.get((from, to))
  def successors(from: Vertex): Option[MS[Vertex]] = nodeList.get(from)
  def predecessors(to: Vertex): Option[MS[Vertex]] = reverseNodeList.get(to)
  def sources: MS[Vertex] = sourceNodes
  def sinks: MS[Vertex] = sinkNodes
  def allNodes: List[Vertex] = nodeLabel.keys.toList
  def allEdges: MS[(Vertex, EdgeLabel, Vertex)] = edgeList
}
