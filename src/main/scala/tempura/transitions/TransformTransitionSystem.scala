package tempura.transitions

import tempura.expression.Core
import tempura.expression.Core.InterpEnv
import tempura.expression.Syntax.BoolExpr
import tempura.expression.transforms.ExprTransformer
import tempura.helpers.Utils.failwith

// apply a transformer to every entry of the transition system
object TransformTransitionSystem {

  private def transformBoolExpr(transform: ExprTransformer)(interpEnv: InterpEnv)(expr: Core.Expr[Core.BoolSort]) : Core.Expr[Core.BoolSort] = {
    transform.transform(interpEnv)(expr) match {
      case BoolExpr(e) => e
      case e =>
        failwith(s"TransformTransitionSystem: expected BoolExpr, but got ${e}")
    }
  }

  def apply(ts: TransitionSystem, transform: ExprTransformer): TransitionSystem = {
    val typeEnv = ts.getTypeEnv
    val interpEnv = Core.TransformInterpEnv(ts.getInterpEnv, transform)
    val bt = transformBoolExpr(transform)(interpEnv)

    val initT = bt(ts.init)
    val transT = TransitionFormula.TransformTransition(ts.trans, transform)
    val propertiesT = ts.properties.map((name, prop) => (name, bt(prop)))
    val assumptionsT = ts.assumptions.map((name, ass) => (name, bt(ass)))
    val livePropertiesT = ts.liveProperties.map((name, liveProp) => (name, bt(liveProp)))
    val liveAssumptionsT = ts.liveAssumptions.map((name, liveAss) => (name, bt(liveAss)))
    val fairAssumptionsT = ts.fairAssumptions.map((name, fairAss) => (name, bt(fairAss)))
    val theoryAxiomsT = ts.theoryAxioms.map((name, tA) => (name, bt(tA)))

    TransitionSystem(initT, transT, propertiesT, assumptionsT, livePropertiesT, liveAssumptionsT,
      fairAssumptionsT, theoryAxiomsT, typeEnv, interpEnv)
  }
}
