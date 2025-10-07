package org.abstractpredicates.repl

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.parsing.ast.{ParseTree, ParseValue, VMTParser}
import org.abstractpredicates.parsing.ast.ParseTree.{INode, Leaf}
import org.abstractpredicates.parsing.parsers.StringToSExprParser
import org.abstractpredicates.repl.TempuCommandResult.{TempuCommandResultExit, TempuCommandResultFailure, TempuCommandResultSuccess}
import org.abstractpredicates.smt.Z3Solver
import org.abstractpredicates.transitions.*
import org.abstractpredicates.helpers.Utils.*
import cats.syntax.all.*
import org.abstractpredicates.parsing.io.TransitionSystemReader

object CommonCommands {

  def stdSexprNameParser(p: ParseTree, n: String) = {
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

  class ParseSExprCommand extends StatelessSExprCommand {
    override def getName: String = "parse"

    override def parseName(name: ParseTree): Boolean = stdSexprNameParser(name, "parse")

    override def getDescription = "(parse <expr>) Parse a given S-expression"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(sexprNode) =>
          TempuCommandResultSuccess(sexprNode.toString)
        case l =>
          TempuCommandResultFailure("Illegal arguments: " + l.mkString(", "))
      }
    }
  }

  class ParseFormulaCommand extends StatelessSExprCommand {
    override def getName: String = "parse-formula"

    override def parseName(name: ParseTree): Boolean = stdSexprNameParser(name, "parse-formula")

    override def getDescription = "(parse-formula <formula>) Parse a formula into internal AST representation (with empty environment)"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(f) =>
          VMTParser.translateFormula(Core.emptyTypeEnv, Core.emptyInterpEnv)(f) match {
            case Right(boxedExpr) =>
              TempuCommandResultSuccess(s"Expression: ${boxedExpr.e} Sort: ${boxedExpr.sort}")
            case Left(err, p) =>
              TempuCommandResultFailure(s"Parsing failure: ${err} @ AST node ${p.toString}")
          }
        case _ => TempuCommandResultFailure("illegal arguments: " + args.mkString(", "))
      }
    }
  }

  class ReadTransitionSystemCommand extends StatelessSExprCommand {
    override def getName: String = "read-transition-system"

    override def parseName(name: ParseTree): Boolean = stdSexprNameParser(name, "read-transition-system")

    override def getDescription = "(read-transition-system <file>) Read a transition system from a file"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(Leaf(ParseValue.PString(filePath))) =>
          println(s"read-transition-system: reading file ${filePath} ...")
          val reader = TransitionSystemReader(filePath)
          reader.readVMT match {
            case Right(pts) =>
              println(s"PreTransitionSystem object: ${pts.toString}")
              TempuCommandResultSuccess(s"read-transition-system: successfully read transition system from file ${filePath}")
            case Left(reason) =>
              TempuCommandResultFailure(s"read-transition-system failed: reason ${reason.toString}")
          }
        case _ =>
          TempuCommandResultFailure(s"read-transition-system: illegal command: ${args.toList.mkString(" ")}")
      }
    }
  }

  class VMTCommand extends StatelessSExprCommand {
    override def getName: String = "vmt"

    override def parseName(name: ParseTree): Boolean = stdSexprNameParser(name, "vmt")

    override def getDescription = "(vmt clear|{parse <str>}|compile-z3) Clear VMT parser state or parse a VMT command string"

    private val pts: PreTransitionSystem = PreTransitionSystem()
    private val solver: Z3Solver.Z3Solver = Z3Solver.Z3Solver(pts.getTypeEnv, pts.getInterpEnv)

    private def showOutput(): String = {
      "Transition System State: \n" + pts.toString
    }

    private def invokeZ3(fmla: ParseTree, doAdd: Boolean) = {
      VMTParser.translateFormula(pts.getTypeEnv, pts.getInterpEnv)(fmla) match {
        case Right(fmlaT) =>
          val fmlaZ3 = solver.lower(fmlaT) 
          if (doAdd) {
            solver.addTerms(List(fmlaZ3)) 
            TempuCommandResultSuccess(s"Added Z3 formula: ${fmlaZ3.toString}")
          } else {
            TempuCommandResultSuccess(s"Lowered Z3 formula: ${fmlaZ3.toString}")
          }
        case Left(reason) =>
          TempuCommandResultFailure(s"Illegal input to compile-z3: ${reason._1} @ ${reason._2}")
      }

    }

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(Leaf(ParseValue.PTerm("clear"))) =>
          pts.clear()
          TempuCommandResultSuccess("Successfully cleared VMT parser state.")
        case List(Leaf(ParseValue.PTerm("parse")), term) =>
          // call VMT parser and interpret the results.
          val result = VMTParser.parse(pts)(term)
          result match {
            case Right(_) =>
              TempuCommandResultSuccess("Successfully parsed VMT statement. \n" + showOutput())
            case Left(reason) =>
              TempuCommandResultFailure(s"Illegal input: ${reason._1} @ ${reason._2}")
          }
        case List(Leaf(ParseValue.PTerm("compile-z3")), fmla) => invokeZ3(fmla, false)
        case List(Leaf(ParseValue.PTerm("assert-z3")), fmla) => invokeZ3(fmla, true)
        case List(Leaf(ParseValue.PTerm("push-z3"))) =>
          solver.push()
          TempuCommandResultSuccess("Successfully pushed Z3 context.")
        case List(Leaf(ParseValue.PTerm("pop-z3"))) =>
          solver.pop()
          TempuCommandResultSuccess("Successfully popped Z3 context.")
        case List(Leaf(ParseValue.PTerm("solve-z3"))) =>
          TempuCommandResultSuccess(s"Z3 Output: ${solver.checkSat()}")
        case List(Leaf(ParseValue.PTerm("reset-z3"))) =>
          solver.reset()
          TempuCommandResultSuccess(s"Successfully reset Z3 solver.")
        case List(Leaf(ParseValue.PTerm("print-env"))) =>
          println(s"Type Environment: ${pts.getTypeEnv.toString}")
          println(s"Interpretation Environment: ${pts.getInterpEnv.toString}")
          TempuCommandResultSuccess("done")
        case List(Leaf(ParseValue.PTerm("declare-sort-z3")), Leaf(ParseValue.PTerm(name))) =>
          val ns = Core.UnInterpretedSort(name, 0)
          pts.getTypeEnv.add(name, ns)
          val z3sort = solver.defineSort(ns) 
          TempuCommandResultSuccess(s"Successfully declared sort ${name} in Z3: ${z3sort.toString}")
        case List(Leaf(ParseValue.PTerm("declare-finite-sort-z3")), Leaf(ParseValue.PTerm(name)), Leaf(ParseValue.PNumber(size))) =>
          val ns = Core.FiniteUniverseSort(name, size)
          pts.getTypeEnv.add(name, ns)
          val z3sort = solver.defineSort(ns) 
          TempuCommandResultSuccess(s"Successfully declared sort ${name} in Z3: ${z3sort.toString}")
        case List(Leaf(ParseValue.PTerm("declare-var-z3")), Leaf(ParseValue.PTerm(varName)), sortExpr) =>
          VMTParser.translateSort(pts.getTypeEnv)(sortExpr) match {
            case Right(sort) =>
              pts.getInterpEnv.add(varName, Core.mkVar(varName, sort))
              val z3var = solver.declareVar(varName, sort) 
              TempuCommandResultSuccess(s"Successfully declared variable ${varName} in Z3: ${z3var.toString}")
            case Left(reason) => TempuCommandResultFailure(s"Error: did not successfully translate sort expression: ${reason}")
          }
        case List(Leaf(ParseValue.PTerm("define-var-z3")), Leaf(ParseValue.PTerm(varName)), sortExpr, varExpr) =>
          (VMTParser.translateSort(pts.getTypeEnv)(sortExpr), VMTParser.translateFormula(pts.getTypeEnv, pts.getInterpEnv)(varExpr)).tupled match {
            case Right(sort, rhs) =>
              rhs.unify(sort) match {
                case Some(unifiedRhs) =>
                  pts.getInterpEnv.add(varName, rhs)
                  solver.defineVar(varName, sort, unifiedRhs) 
                  TempuCommandResultSuccess(s"Successfully defined ${varName} = ${unifiedRhs}")
                case None =>
                  TempuCommandResultFailure(s"Error: define-var: cannot unify ${rhs.toString} with ${sort.toString}")
              }
            case Left(reason) => TempuCommandResultFailure(s"Error: did not successfully translate define-var expression: ${reason}")
          }
        case l =>
          TempuCommandResultFailure("Illegal input: " + l.mkString(" "))
      }
    }
  }

  class TypeOfSExprCommand extends StatelessSExprCommand {
    override def getName: String = "ast-type-of"

    override def parseName(name: ParseTree): Boolean = stdSexprNameParser(name, "ast-type-of")

    override def getDescription = "(ast-type-of <expr>) Print type of each AST node in parsed representation of S-expression"

    private def typeOfString(p: ParseTree): String = {
      p match {
        case Leaf(ParseValue.PTerm(t)) => s"Term(${t})"
        case Leaf(ParseValue.PString(s)) => s"String(${s})"
        case Leaf(ParseValue.PNumber(n)) => s"Number(${n})"
        case Leaf(ParseValue.PBool(b)) => s"Bool(${b})"
        case INode(l) => "[" + l.map(typeOfString).mkString(", ") + "]"
      }
    }

    override def apply(args: ParseTree*): TempuCommandResult =
      args.toList match {
        case List(t) =>
          TempuCommandResultSuccess(typeOfString(t))
        case _ =>
          TempuCommandResultFailure(s"incorrect number of arguments: ${args.toList.mkString(", ")}")
      }
  }


  class NestedDispatcherCommand(val state: TempuScriptState[ParseTree], var dispatchers: Map[String, TempuCommandDispatcher[ParseTree]])
    extends StatelessSExprCommand {
    override def getName: String = "switch"

    var curr: Option[(String, TempuCommandDispatcher[ParseTree])] = None

    def switch(dispatcherName: String): Boolean = {
      dispatchers.get(dispatcherName) match {
        case Some(d) =>
          curr = Some(dispatcherName, d)
          true
        case None =>
          false
      }
    }

    def leave(): Unit = curr = None

    override def parseName(name: ParseTree): Boolean = {
      stdSexprNameParser(name, "")
    }

    override def getDescription: String =
      "(switch <REPL name>|show|list|drop) Switch between different REPLs by name. Available REPLs: [" + dispatchers.toList.map(x => x._1).mkString(", ") + "]"

    override def apply(args: ParseTree*): TempuCommandResult = {
      args.toList match {
        case List(Leaf(ParseValue.PTerm("show"))) =>
          curr match {
            case Some(d) => TempuCommandResult.TempuCommandResultSuccess(s"Current REPL is ${d._1}")
            case None => TempuCommandResult.TempuCommandResultSuccess("No REPL selected.")
          }
        case List(Leaf(ParseValue.PTerm("list"))) =>
          TempuCommandResult.TempuCommandResultSuccess(dispatchers.toList.map(x => x._1).mkString(", "))
        case List(Leaf(ParseValue.PTerm("drop"))) =>
          leave()
          TempuCommandResult.TempuCommandResultSuccess("Dropped REPL context.")
        case List(Leaf(ParseValue.PTerm(d))) =>
          switch(d) match {
            case true => TempuCommandResult.TempuCommandResultSuccess(s"Switched to REPL ${d}.")
            case false => TempuCommandResult.TempuCommandResultFailure(s"REPL ${d} not found; switching failed.")
          }
        case List(_, _*) => failwith("TODO")
        case Nil => failwith("TODO")
      }
    }
  }

  class NestedDispatcher(d: NestedDispatcherCommand)
    extends TempuCommandDispatcher[ParseTree](d.state, Set(d)) {
    override def dispatch(input: List[ParseTree]): TempuCommandResult = {
      (input, d.curr) match {
        case (i, Some(currDispatcher)) if i != ParseTree.Leaf(ParseValue.PTerm("switch")) =>
          currDispatcher._2.dispatch(input)
        case _ =>
          super.dispatch(input)
      }
    }
  }
}
