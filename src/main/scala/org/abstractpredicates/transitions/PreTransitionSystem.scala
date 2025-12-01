package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.expression.Core
import cats.implicits.*
import org.abstractpredicates.helpers.Utils.AccumulatingEntry

// A `PreTransitionSystem` instance
// represents a transition system that is being built by dynamically parsing
// a transition system specification from either the command line or a file.
class PreTransitionSystem {
  
  private var typeEnv: Core.TypeEnv = Core.emptyTypeEnv
  private var interpEnv: Core.InterpEnv = Core.emptyInterpEnv
  private var init: Option[Core.Expr[Core.BoolSort]] = None

  def this(te: Core.TypeEnv, ie: Core.InterpEnv) = {
    this()
    typeEnv = te
    interpEnv = ie
  }
  
  def setTypeEnv(te: Core.TypeEnv): Unit = this.typeEnv = te
  def getTypeEnv: Core.TypeEnv = this.typeEnv
  def setInterpEnv(ie: Core.InterpEnv): Unit = this.interpEnv = ie 
  def getInterpEnv: InterpEnv = this.interpEnv
  def setInit(cond: Core.Expr[Core.BoolSort]) = this.init = Some(cond)  
  def getInit: Option[Core.Expr[Core.BoolSort]]= this.init 
  
  val stateVars: AccumulatingEntry[TimedVariable] = AccumulatingEntry[TimedVariable]("state-vars")
  val properties: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("properties")
  val assumptions: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("assumptions")
  val liveProperties: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("live-properties")
  val theoryAxioms: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("theory-axioms")
  val fairnessAssumptions: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("fairness-assumptions")
  val liveAssumptions: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("live-assumptions")
  val transitions: AccumulatingEntry[Core.Expr[Core.BoolSort]] = AccumulatingEntry[Core.Expr[Core.BoolSort]]("transitions")

  def toTransitionSystem: Option[TransitionSystem] = {
    init map {
      initCond =>
        new TransitionSystem(
          stateVars.get.map(x => x._2).toSet,
          initCond,
          transitions.get,
          properties.get,
          assumptions.get,
          liveProperties.get,
          liveAssumptions.get,
          fairnessAssumptions.get,
          theoryAxioms.get,
          typeEnv, 
          interpEnv)

    }
  }

  // destroy any recorded state and reset to initial state.
  def clear(): Unit =
    this.typeEnv = Core.emptyTypeEnv
    this.interpEnv = Core.emptyInterpEnv
    this.init = None
    this.transitions.reset()
    this.stateVars.reset()
    this.properties.reset()
    this.assumptions.reset()
    this.liveProperties.reset()
    this.theoryAxioms.reset()
    this.fairnessAssumptions.reset()

  override def toString: String =
    val b = new StringBuilder
    b.append("PreTransitionSystem:\n")
    b.append(s"  stateVars (${stateVars.length}): ${if stateVars.isEmpty then "<none>" else stateVars.toString}\n")
    b.append(s"  init: ${init.map(_.toString).getOrElse("<unset>")}\n")
    b.append(s"  trans: ${transitions}\n")
    b.append(properties).append("\n")
    b.append(assumptions).append("\n")
    b.append(liveProperties).append("\n")
    b.append(fairnessAssumptions).append("\n")
    b.append(s"  typeEnv: $typeEnv\n")
    b.append(s"  interpEnv: $interpEnv")
    b.toString
}
