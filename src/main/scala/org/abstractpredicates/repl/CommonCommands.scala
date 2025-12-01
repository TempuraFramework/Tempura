package org.abstractpredicates.repl

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.parsing.sexpr.{ParseTree, ParseValue, SmtlibParser, StringToSExprParser, VMTParser}
import org.abstractpredicates.parsing.sexpr.ParseTree.{INode, Leaf}
import org.abstractpredicates.repl.TempuCommandResult.{TempuCommandResultExit, TempuCommandResultFailure, TempuCommandResultSuccess}
import org.abstractpredicates.smt.Z3Solver
import org.abstractpredicates.transitions.*
import org.abstractpredicates.helpers.Utils.*
import cats.syntax.all.*
import org.abstractpredicates.helpers.{ReplRegistry, TransformRegistry, Transforms}
import org.abstractpredicates.parsing.io.TDLReader
import org.abstractpredicates.helpers.Transforms.*

object CommonCommands {

  private def stdSexprNameParser(p: ParseTree, n: String) = {
    p match {
      case Leaf(ParseValue.PTerm(t)) if t == n => true
      case _ => false
    }
  }

  trait StatefulCommand[T](val state: TempuScriptState[T]) extends TempuCommand[T]

  abstract class StatefulSExprCommand(s: TempuScriptState[ParseTree]) extends StatefulCommand[ParseTree](s)

  trait StatelessSExprCommand extends TempuCommand[ParseTree]

  class HistoryCommandStateful(s: TempuScriptState[ParseTree]) extends StatefulSExprCommand(s) {
    override def getName: String = "history"

    override def parseName(name: ParseTree): Boolean = {
      stdSexprNameParser(name, "history")
    }

    override def getDescription: String = "(history) Returns history of commands"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List() => TempuCommandResult.TempuCommandResultSuccess(state.vectorized.mkString("\n  "))
        case List(Leaf(ParseValue.PTerm("clear"))) =>
          state.clearHistory()
          TempuCommandResult.TempuCommandResultSuccess("History cleared.")
        case l => TempuCommandResult.TempuCommandResultFailure("too many arguments: " + l.mkString(", "))
      }
    }

    override def toString: String = "(history)"
  }

  class ExitCommand extends StatelessSExprCommand {
    override def getName: String = "exit"

    override def parseName(name: ParseTree) = stdSexprNameParser(name, "exit")

    override def getDescription = "(exit) Exit the entire program"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(Leaf(ParseValue.PNumber(exitCode))) =>
          TempuCommandResultExit(s"Exiting... (Code ${exitCode})", exitCode)
        case List() =>
          TempuCommandResultExit("Exiting... (Code 0)", 0)
        case _ =>
          TempuCommandResultExit("Exiting... (Code 255)", 255)
      }
    }
  }

  class InterpreterCommand extends StatelessSExprCommand {
    override def getName: String = "eval"

    override def parseName(name: ParseTree) = stdSexprNameParser(name, "exit")

    override def getDescription: String = ""

    def parseSolver(args: List[ParseTree]): TempuCommandResult = {
      ???
    }

    def parsePipelineStage(args: ParseTree): Either[String, ReplRegistry.PipelineStage] =
      args match {
        case INode(List(Leaf(ParseValue.PTerm("with")), Leaf(ParseValue.PTerm(typeEnvName)), Leaf(ParseValue.PTerm(interpEnvName)), Leaf(ParseValue.PTerm(passName)))) =>
          TransformRegistry(passName) match {
            case Some(b: Transforms.BoxedEnvTransform) =>
              Right({ (x: ReplRegistry.Value) =>
                x.value match {
                  case b.transform.aTag(input) =>
                    ReplRegistry.wrap(b.transform(Core.emptyTypeEnv, Core.emptyInterpEnv)(input))
                  case _ => Left(s"error: supplied value ${x.value} does not type-check with ${b.transform.aTag.toString}")
                }
              })
            case Some(e) => Left(s"error: expected ${passName} to be an environmental transform but got ${e} instead ")
            case None => Left(s"error: couldn't find ${passName} in registry of transforms; available options: ${TransformRegistry.toString}")
          }
        case _ => ???
      }

    def parsePipeline(args: List[ParseTree]): TempuCommandResult = {
      ???
    }

    def parseNew(args: List[ParseTree]): TempuCommandResult = {
      args match {
        case List(Leaf(ParseValue.PTerm("val")), Leaf(ParseValue.PTerm(valName)), Leaf(ParseValue.PString(valValue))) => ???
        case List(Leaf(ParseValue.PTerm("type-env")), Leaf(ParseValue.PTerm(envName))) => ???
        case List(Leaf(ParseValue.PTerm("env")), Leaf(ParseValue.PTerm(envName))) => ???
        case Leaf(ParseValue.PTerm("solver")) :: Leaf(ParseValue.PTerm(solverName)) :: rest =>
          parseSolver(rest)
        case Leaf(ParseValue.PTerm("pipeline")) :: Leaf(ParseValue.PTerm(pipelineName)) :: rest =>
          parsePipeline(rest)

      }
    }

    def parseApply(args: List[ParseTree]): TempuCommandResult = {
      ???
    }

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case Leaf(ParseValue.PTerm("new")) :: rest => parseNew(rest)
        case Leaf(ParseValue.PTerm("apply")) :: rest => ???
      }
    }
  }

}
