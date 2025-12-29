package tempura.transitions

import scala.collection.mutable.Map as MM
import scala.collection.mutable.Set as MS
import scala.collection.immutable.Map as IM
import scala.collection.immutable.Set as IS
import tempura.expression.Syntax.*
import tempura.helpers.Utils.*
import cats.implicits.*

import scala.collection.mutable

class LabeledGraph[NodeLabel, EdgeLabel] {

  type Vertex = Int
  type Edge = (Vertex, EdgeLabel, Vertex)

  private var numNodes = 0
  private var numEdges = 0

  // vertex => vertex label map
  private val nodeLabel: MM[Vertex, NodeLabel] = mutable.Map()
  // edge => edge label map
  private val edgeLabel: MM[(Vertex, Vertex), EdgeLabel] = mutable.Map()
  // for each u, nodeList(u) = {(u, v)}
  private val nodeList: MM[Vertex, MS[Vertex]] = mutable.Map()
  // for each v, reverseNodeList(v) = {(u, v)}
  private val reverseNodeList: MM[Vertex, MS[Vertex]] = mutable.Map()
  // list of all weighted edges
  private val edgeList: MS[(Vertex, EdgeLabel, Vertex)] = mutable.Set()

  private val sourceNodes: MS[Vertex] = mutable.Set()
  private val sinkNodes: MS[Vertex] = mutable.Set()
  
  private val labelToNode: MM[NodeLabel, Vertex] = mutable.Map()
  private val labelToEdge: MM[(Vertex, Vertex), Edge]  = mutable.Map() 

  def this(vertices: (Int, NodeLabel, List[(EdgeLabel, Int)])*) = {
    this()
    // first maintain nodeLabel, nodeList, edgeLabel, edgeList
    vertices foreach {
      entry =>
        val vtx = entry._1
        val weight = entry._2
        val adjacencies = entry._3
        nodeList.update(vtx, mutable.Set())
        reverseNodeList.update(vtx, mutable.Set())
        nodeLabel.get(vtx) match {
          case Some(_) => failwith(s"Error: duplicate definition of ${vtx} in LabeledGraph")
          case None =>
            labelToNode.update(weight, vtx)
            nodeLabel.update(vtx, weight)
            adjacencies foreach {
              out =>
                nodeList(vtx).add(out._2)
                edgeLabel.update((vtx, out._2), out._1)
                edgeList.add((vtx, out._1, out._2))
                labelToEdge.update((vtx, out._2), (vtx, out._1, out._2))
            }
        }
    }
    // next maintain reverseNodeList
    nodeList foreach {
      (in, succs) =>
        succs foreach {
          out =>
            reverseNodeList.get(out) match {
              case Some(s) =>
                s.add(in)
              case None =>
                reverseNodeList.update(out, mutable.Set(in))
            }
        }
    }
    // finally maintain sourceNodes, sinkNodes
    nodeList foreach {
      (x, xOut) =>
        assert(reverseNodeList.contains(x))
        if (xOut.isEmpty) then {
          sinkNodes.add(x)
        }
    }
    reverseNodeList foreach {
      (x, xIn) =>
        if (xIn.isEmpty) then {
          sourceNodes.add(x)
        }
    }
  }

  def addNode(label: NodeLabel): Vertex = {
    val vtx = numNodes
    addNode(vtx, label)
    vtx
  }

  def addNode(vertex: Vertex, lbl: NodeLabel): Vertex = {
    if (nodeList.contains(vertex)) failwith(s"Error: duplicate definition of ${vertex} in LabeledGraph")
    nodeLabel.update(vertex, lbl)
    nodeList.update(vertex, mutable.Set())
    labelToNode.update(lbl, vertex)
    reverseNodeList.update(vertex, mutable.Set())
    sinkNodes += vertex
    sourceNodes += vertex
    numNodes += 1
    vertex
  }

  def nodeOfLabel(label: NodeLabel): Option[Vertex] = labelToNode.get(label)
  
  def edgeOfLabel(from: Vertex, to: Vertex): Option[Edge] = labelToEdge.get((from, to))
  
  def addEdge(from: Vertex, to: Vertex, label: EdgeLabel): Option[(Vertex, EdgeLabel, Vertex)] = {
    (nodeLabel.get(from), nodeLabel.get(to)).tupled match {
      case Some(_, _) =>
        // Check if edge already exists before adding
        val edge = (from, label, to)
        if (edgeList.contains(edge)) {
          None // Edge already exists, return None to signal no change
        } else {
          labelToEdge.update((from, to), edge)
          if sourceNodes.contains(to) then sourceNodes.remove(to)
          if sinkNodes.contains(from) then sinkNodes.remove(from)
          nodeList.update(from, nodeList.getOrElse(from, MS()) + to)
          reverseNodeList.update(to, reverseNodeList.getOrElse(to, MS()) + from)
          edgeList += edge
          edgeLabel.update((from, to), label)
          Some(edge)
        }
      case None => None
    }
  }

  def removeNode(node: Vertex): Unit = {
    labelToNode.remove(labelOf(node).get)
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
    labelToEdge.remove((from, to))
    nodeList.get(from) match {
      case Some(fromSucc) =>
        fromSucc.remove(to)
      case None => ()
    }
    reverseNodeList.get(to) match {
      case Some(toPred) =>
        toPred.remove(from)
      case None => ()
    }
    val weight = edgeLabel((from, to))
    edgeList.remove((from, weight, to))
    edgeLabel.remove((from, to))
    nodeList(from).remove(to)
    reverseNodeList(to).remove(from)
    if nodeList(from).isEmpty then sinkNodes.add(from)
    if reverseNodeList(to).isEmpty then sourceNodes.add(to)
  }

  def hasEdge(from: Vertex, to: Vertex): Boolean = edgeLabel.contains((from, to))

  def labelOf(node: Vertex): Option[NodeLabel] = nodeLabel.get(node)

  def labelOf(from: Vertex, to: Vertex): Option[EdgeLabel] = edgeLabel.get((from, to))

  def successors(from: Vertex): Option[MS[Vertex]] = nodeList.get(from)

  def predecessors(to: Vertex): Option[MS[Vertex]] = reverseNodeList.get(to)

  def sources: MS[Vertex] = sourceNodes

  def sinks: MS[Vertex] = sinkNodes

  def allNodes: List[Vertex] = nodeList.keys.toList

  def allEdges: MS[(Vertex, EdgeLabel, Vertex)] = edgeList

  def subgraph(delta: Vertex => Set[Vertex])(start: Set[Vertex], forwards: Boolean): LabeledGraph[NodeLabel, EdgeLabel] = {
    val worklist: mutable.Queue[Vertex] = mutable.Queue()
    val subgraph: LabeledGraph[NodeLabel, EdgeLabel] = LabeledGraph()

    start foreach {
      v =>
        worklist.enqueue(v)
        subgraph.addNode(v, labelOf(v).get)
    }

    while (worklist.nonEmpty) {
      val u = worklist.dequeue()
      delta(u) foreach {
        v =>
          worklist.enqueue(v)
          subgraph.addNode(v, labelOf(v).get)
          if forwards then {
            subgraph.addEdge(u, v, labelOf(u, v).get)
          } else {
            subgraph.addEdge(v, u, labelOf(v, u).get)
          }
      }
    }
    subgraph
  }

  def backwardsClosed(vs: Set[Vertex]): LabeledGraph[NodeLabel, EdgeLabel] = {
    subgraph(x => this.predecessors(x) match {
      case Some(ls) => ls.toSet
      case None => Set()
    })(vs, forwards = false)
  }

  def forwardsClosed(vs: Set[Vertex]): LabeledGraph[NodeLabel, EdgeLabel] = {
    subgraph(x => this.successors(x) match {
      case Some(ls) => ls.toSet
      case None => Set()
    })(vs, forwards = true)
  }
}

trait BoxedLabeledGraph {
  type NodeLabel
  type EdgeLabel
  val graph: LabeledGraph[NodeLabel, EdgeLabel]
}

object BoxedLabeledGraph {
  def make[N, E](g: LabeledGraph[N, E]) =
    new BoxedLabeledGraph {
      override type NodeLabel = N
      override type EdgeLabel = E
      override val graph = g
    }
}