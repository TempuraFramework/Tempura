package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core.TypeEnv
import org.abstractpredicates.expression.Core

import cats.implicits.*

// A `PreTransitionSystem` instance
// represents a transition system that is being built by dynamically parsing
// a VMT-style input from either the command line or a file.
class PreTransitionSystem {

  private var typeEnv: Core.TypeEnv = Core.emptyTypeEnv
  private var interpEnv: Core.InterpEnv = Core.emptyInterpEnv
  private var stateVars: List[TimedVariable] = List[TimedVariable]()
  private var init: Option[Core.Expr[Core.BoolSort]] = None
  private var trans: Option[Core.Expr[Core.BoolSort]] = None
  private var assertions: List[Core.Expr[Core.BoolSort]] = List()
  private var assumptions: List[Core.Expr[Core.BoolSort]] = List()
  private var liveAssertions: List[Core.Expr[Core.BoolSort]] = List()
  private var liveAssumptions: List[Core.Expr[Core.BoolSort]] = List()
  private var fairness: List[Core.Expr[Core.BoolSort]] = List()
  private var actionset: List[String] = List()

  def getTypeEnv: TypeEnv = typeEnv

  def setTypeEnv(env: Core.TypeEnv): Unit = typeEnv = env

  def getInterpEnv: Core.InterpEnv = interpEnv

  def setInterpEnv(env: Core.InterpEnv): Unit = interpEnv = env

  def getStateVars: List[TimedVariable] = stateVars

  def setStateVars(vars: List[TimedVariable]): Unit = stateVars = vars

  def getInit: Option[Core.Expr[Core.BoolSort]] = init

  def setInit(e: Core.Expr[Core.BoolSort]): Unit = init = Some(e)

  def getTrans: Option[Core.Expr[Core.BoolSort]] = trans

  def setTrans(e: Core.Expr[Core.BoolSort]): Unit = trans = Some(e)

  def getAssertions: List[Core.Expr[Core.BoolSort]] = assertions

  def setAssertions(e: List[Core.Expr[Core.BoolSort]]): Unit = assertions = e

  def getAssumptions: List[Core.Expr[Core.BoolSort]] = assumptions

  def setAssumptions(e: List[Core.Expr[Core.BoolSort]]): Unit = assumptions = e

  def getLiveAssertions: List[Core.Expr[Core.BoolSort]] = liveAssertions

  def setLiveAssertions(e: List[Core.Expr[Core.BoolSort]]): Unit = liveAssertions = e

  def getFairness: List[Core.Expr[Core.BoolSort]] = fairness

  def setFairness(e: List[Core.Expr[Core.BoolSort]]): Unit = fairness = e

  def getActionset: List[String] = actionset

  def setActionset(e: List[String]): Unit = actionset = e

  def addStateVar(v: TimedVariable): Unit = stateVars = v :: stateVars

  def addAction(a: String): Unit = actionset = a :: actionset

  def addAssertion(a: Core.Expr[Core.BoolSort]): Unit = assertions = a :: assertions

  def addAssumption(a: Core.Expr[Core.BoolSort]): Unit = assumptions = a :: assumptions

  def addLiveAssertion(a: Core.Expr[Core.BoolSort]): Unit = liveAssertions = a :: liveAssertions

  def addLiveAssumption(a: Core.Expr[Core.BoolSort]): Unit = liveAssumptions = a :: liveAssumptions

  def addFairness(a: Core.Expr[Core.BoolSort]): Unit = fairness = a :: fairness

  def toTransitionSystem: Option[TransitionSystem] =
    (init, trans).tupled.map(x =>
      new TransitionSystem(stateVars, x._1, x._2, assertions, assumptions, liveAssertions, liveAssumptions, fairness, typeEnv, interpEnv))

  // destroy any recorded state and reset to initial state.
  def clear(): Unit =
    this.typeEnv = Core.emptyTypeEnv
    this.interpEnv = Core.emptyInterpEnv
    this.stateVars = List[TimedVariable]()
    this.init = None
    this.trans = None
    this.assertions = List()
    this.assumptions = List()
    this.liveAssertions = List()
    this.liveAssumptions = List()
    this.fairness = List()
    this.actionset = List()

  override def toString: String =
    def fmtList[A](title: String, xs: List[A]): String =
      if xs.isEmpty then s"$title (0): <none>"
      else s"$title (${xs.length}):\n    - ${xs.reverse.mkString("\n    - ")}"

    val b = new StringBuilder
    b.append("PreTransitionSystem:\n")
    b.append(s"  stateVars (${stateVars.length}): ${if stateVars.isEmpty then "<none>" else stateVars.reverse.mkString(", ")}\n")
    b.append(s"  actions (${actionset.length}): ${if actionset.isEmpty then "<none>" else actionset.reverse.mkString(", ")}\n")
    b.append(s"  init: ${init.map(_.toString).getOrElse("<unset>")}\n")
    b.append(s"  trans: ${trans.map(_.toString).getOrElse("<unset>")}\n")
    b.append(fmtList("  assertions", assertions)).append("\n")
    b.append(fmtList("  assumptions", assumptions)).append("\n")
    b.append(fmtList("  liveAssertions", liveAssertions)).append("\n")
    b.append(fmtList("  liveAssumptions", liveAssumptions)).append("\n")
    b.append(fmtList("  fairness", fairness)).append("\n")
    b.append(s"  typeEnv: $typeEnv\n")
    b.append(s"  interpEnv: $interpEnv")
    b.toString
}
