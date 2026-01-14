package tempura.liveness

import tempura.cozy.AutoRegister
import tempura.cozy.Transforms.*
import tempura.expression.Core
import tempura.smt.SmtSolver
import tempura.transitions.States.StateGraph
import tempura.transitions.TransitionSystem

@AutoRegister("synth-rel-ranking")
object RelationalRankingSynthesizer extends Transform[(SmtSolver.SolverEnvironment, TransitionSystem, StateGraph, Core.BoxedExpr), Tuple1[Core.Expr[Core.BoolSort]]] {

  // TODO

  override def apply(args : (SmtSolver.SolverEnvironment, TransitionSystem, StateGraph, Core.BoxedExpr))
    : Either[String, Tuple1[Core.Expr[Core.BoolSort]]] = ???

}
