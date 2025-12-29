package tempura.temporal

import tempura.expression.Core.*
import tempura.expression.Syntax.*
import tempura.transitions.States.{State, StateGraph, StatePair}
import tempura.expression.Core
import tempura.transitions.{LabeledGraph, TransitionSystem}

object CTL {

  def mkEX(fmla: Expr[BoolSort]): Expr[BoolSort] =
    Core.mkUop("EX", fmla, BoolSort())

  def mkEG(fmla: Expr[BoolSort]): Expr[BoolSort] =
    Core.mkUop("EG", fmla, BoolSort())

  def mkEU(before: Expr[BoolSort], until: Expr[BoolSort]): Expr[BoolSort] =
    Core.mkBop("EU", before, until, BoolSort())

  object IsEX {
    def unapply(fmla: BoxedExpr): Option[Core.Expr[Core.BoolSort]] = {
      fmla match {
        case BoolExpr(e) =>
          e match {
            case Uop("EX", BoolExpr(fmla), Core.BoolSort()) => Some(fmla)
            case _ => None
          }
        case _ => None
      }
    }
  }

  object IsEG {
    def unapply(fmla: BoxedExpr): Option[Expr[BoolSort]] = {
      fmla match {
        case BoolExpr(e) =>
          e match {
            case Uop("EG", BoolExpr(fmla), Core.BoolSort()) => Some(fmla)
            case _ => None
          }
        case _ => None
      }
    }
  }

  object ISEU {
    def unapply(fmla: BoxedExpr): Option[(Expr[BoolSort], Expr[BoolSort])] = {
      fmla match {
        case BoolExpr(e) =>
          e match {
            case Bop("EU", BoolExpr(before), BoolExpr(after), Core.BoolSort()) =>
              Some((before, after))
            case _ => None
          }
        case _ => None
      }
    }
  }

  enum Direction(val init: StateGraph => Set[StateGraph#Vertex], val delta: State => StateGraph) {
    
    case Forward(i: StateGraph => Set[StateGraph#Vertex], d: State => StateGraph) extends Direction(i, d)
    case Backward(i: StateGraph => Set[StateGraph#Vertex], d: State => StateGraph) extends Direction(i, d)
  }

  case class CTLProperty(fmla: Expr[BoolSort], trs: TransitionSystem, dir: Direction) {
    var stateGraph: StateGraph = LabeledGraph()
  }
}
