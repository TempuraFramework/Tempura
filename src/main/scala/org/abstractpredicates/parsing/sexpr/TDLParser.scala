package org.abstractpredicates.parsing.sexpr

import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.transitions.{PreTransitionSystem, TimedVariable, TransitionSystem}
import org.abstractpredicates.parsing.sexpr.ParseTree.*
import org.abstractpredicates.parsing.sexpr.ParseValue.*
import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.helpers.Transforms.EnvTransform

import scala.annotation.tailrec
import scala.reflect.ClassTag

object TDLParser extends EnvTransform[List[ParseTree], TransitionSystem](using summon[ClassTag[List[ParseTree]]], summon[ClassTag[TransitionSystem]]) {

  def parse(typeEnv: TypeEnv, interpEnv: InterpEnv)(p: PreTransitionSystem, tree: ParseTree): Either[String, PreTransitionSystem] = {
    tree match {
      case INode(List(Leaf(PTerm("state-var")), Leaf(PTerm(varName)), varSort, Leaf(PTerm(":next")), Leaf(PTerm(nextVarName)))) =>
        SmtlibParser.parseSort(typeEnv)(varSort) match {
          case Right(parsedSort) =>
            interpEnv |- (varName, parsedSort)
            val timedVar = TimedVariable(varName, nextVarName, 0, parsedSort)
            p.stateVars.add(timedVar)
            Right(p)
          case Left(reason) => Left(reason.toString)
        }
      case INode(List(Leaf(PTerm("vmtlib")), smtlibStmt)) =>
        VMTParser.parse(typeEnv, interpEnv)(p)(smtlibStmt) match {
          case Right(_) => Right(p)
          case Left(error) => Left(error.toString)
        }
      case INode(List(Leaf(PTerm("init")), initCond)) =>
        SmtlibParser(typeEnv, interpEnv)(initCond) match {
          case Right(fmla) =>
            fmla.unify(Core.boolSort) match {
              case Some(b) =>
                p.setInit(b)
                Right(p)
              case None =>
                Left(s"Initial condition needs to be a boolean expression, but got ${fmla.toString}")
            }
          case Left(error) => Left(error)
        }
      case INode(List(Leaf(PTerm("transition")), transitionCond)) =>
        SmtlibParser(typeEnv, interpEnv)(transitionCond) match {
          case Right(BoolExpr(fmla)) =>
            p.transitions.add(fmla)
            Right(p)
          case _ => Left(s"malformed transition formula definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("transition")), transitionCond, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(transitionCond) match {
          case Right(BoolExpr(fmla)) =>
            p.transitions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed transition formula definition: ${tree}")

        }
      case INode(List(Leaf(PTerm("theory-axiom")), ax)) =>
        SmtlibParser(typeEnv, interpEnv)(ax) match {
          case Right(BoolExpr(fmla)) =>
            p.theoryAxioms.add(fmla)
            Right(p)
          case _ => Left(s"malformed theory axiom definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("theory-axiom")), ax, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(ax) match {
          case Right(BoolExpr(fmla)) =>
            p.theoryAxioms.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed theory axiom ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("property")), prop)) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.properties.add(fmla)
            Right(p)
          case _ => Left(s"malformed property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("property")), prop, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.properties.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed property ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("assumption")), assumed)) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.assumptions.add(fmla)
            Right(p)
          case _ => Left(s"malformed assumption definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("assumption")), assumed, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.assumptions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed assumption ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-property")), prop)) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.liveProperties.add(fmla)
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-property")), prop, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.liveProperties.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("fair-assumption")), assumed)) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.fairnessAssumptions.add(fmla)
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("fair-assumption")), assumed, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.fairnessAssumptions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case _ =>
        Left(s"TDLParser: unexpected input ${tree.toString}")
    }
  }

  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(a: List[ParseTree]): Either[String, TransitionSystem] = {
    val pts = PreTransitionSystem()
    pts.setTypeEnv(typeEnv)
    pts.setInterpEnv(interpEnv)

    @tailrec def aux(l: List[ParseTree]): Either[String, PreTransitionSystem] = {
      l match {
        case a :: t =>
          parse(typeEnv, interpEnv)(pts, a) match {
            case Left(error) => Left(error)
            case Right(_) => aux(t)
          }
        case List() => Right(pts)
      }
    }

    aux(a) match {
      case Right(_) =>
        pts.toTransitionSystem match {
          case Some(ts) => Right(ts)
          case None => Left("error: initialization condition not set")
        }
      case Left(error) => Left(error)
    }
  }
}
