package tempura.liveness

import tempura.cozy.Transforms.*
import tempura.expression.Core
import tempura.smt.SmtSolver
import tempura.transitions.States.{State, StateGraph, StatePair}
import tempura.transitions.TransitionSystem

import scala.collection.mutable
import scala.collection.mutable.{ArrayDeque as Queue, Map as MMap}

object IndexTermMiner extends Transform[(SmtSolver.SolverEnvironment, TransitionSystem, StateGraph), Tuple1[Core.BoxedExpr]] {

  private def synthTerm[S <: Core.Sort[S]](solverEnv: SmtSolver.SolverEnvironment)
                                          (x: (TransitionSystem, StateGraph), t: Core.Expr[S])
  : Either[(StatePair, StatePair), Core.BoxedExpr] =
    val trs = x._1
    val graph = x._2
    val sinks = graph.sinks
    val fair = Core.mkAnd(trs.fairAssumptions.map(x => x._2))
    val queue: Queue[(Core.BoxedExpr, graph.Vertex)] = mutable.ArrayDeque()
    val termVal: MMap[Core.BoxedExpr, StatePair] = mutable.Map()
    sinks.foreach(sink =>
      graph.predecessors(sink).get.foreach(
        pred =>
          val trans = graph.labelOf(pred, sink).get
          if trans.isFair(fair) then {
            termVal.update(trans.model.evaluate(t), trans)
            queue.append((trans.model.evaluate(t).box(), pred))
          }
      )
    )
    var cex: Option[(StatePair, StatePair)] = None
    while (queue.nonEmpty && cex.isEmpty) {
      val front = queue.removeHead()
      val vtx = front._2
      val prevVal = front._1
      graph.predecessors(vtx).get.foreach(pred =>
        val trans = graph.labelOf(pred, vtx).get
        if trans.isFair(fair) then {
          val termValue = trans.model.evaluate(t)
          if prevVal == termValue then {
            cex = Some((trans, termVal(prevVal)))
          } else termVal.get(termValue) match {
            case Some(sp) =>
              cex = Some((trans, sp))
            case None =>
              termVal.update(termValue, trans)
              queue.append((termValue.box(), pred))
          }
        }
      )
    }
    cex match {
      case Some(ex) => Left(ex)
      case None => Right(t)
    }


  private def enumerateTerms(solverEnv: SmtSolver.SolverEnvironment)(trs: TransitionSystem, graph: StateGraph): Option[Core.BoxedExpr] = {
    var foundTerm : Option[Core.BoxedExpr] = None
    val queue : Queue[(String, Core.BoxedSort)] = mutable.ArrayDeque()
    val groundTerms : Set[(String, Core.BoxedSort)] = trs.getStateVars.map(x => (x.getOriginalName, x.getSort)) ++ trs.getTransitionVars
    groundTerms.foreach(x =>
      println(s" * indexTermSynthesis: ... considering ${x} of sort ${x._2.sort}")
      queue.append(x))
    while (foundTerm.isEmpty && queue.nonEmpty) {
      val candidate = queue.removeHead()
      println(" * indexTermSynthesis: trying candidate " + candidate)
      val result = synthTerm(solverEnv)((trs, graph), Core.mkVar(candidate._1, candidate._2))
      result match {
        case Left(ex) => ()
        case Right(t) => foundTerm = Some(t)
      }
    }
    foundTerm
  }

  override def apply(args: (SmtSolver.SolverEnvironment, TransitionSystem, StateGraph)): Either[String, Tuple1[Core.BoxedExpr]] = {
    val solver = args._1 
    enumerateTerms(solver)(args._2, args._3) match {
      case None => Left("no index term found")
      case Some(t) => Right(Tuple1(t))
    }
  }
}
