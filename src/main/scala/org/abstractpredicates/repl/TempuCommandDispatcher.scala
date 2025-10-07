package org.abstractpredicates.repl

import org.abstractpredicates.parsing.ast.ParseTree
import org.abstractpredicates.repl.CommonCommands.StatefulCommand
import org.abstractpredicates.repl.TempuCommandResult.*


class TempuCommandDispatcher[T](val state: TempuScriptState[T], var commands: Set[TempuCommand[T]]) {

  def getCommands: Set[TempuCommand[T]] = commands

  def addCommand(cmd: TempuCommand[T]) : Unit = {
    commands += cmd
  }

  def lookupCommand(cmdName: T) : Option[TempuCommand[T]] = {
    commands.collectFirst { case x if x.parseName(cmdName) => x }
  }

  def help() : List[String] = {
    commands.map(x => x.getDescription).toList
  }

  def helpStr() : String = "Available commands: \n  - " + help().mkString("\n  - ") + "\n"

  def dispatch(input: List[T]) : TempuCommandResult = {
    input match {
      case List() => TempuCommandResultSuccess("")
      case cmdStr :: args =>
        lookupCommand(cmdStr).map(cmd => (cmd(args*), cmd)) match {
          case Some(r: TempuCommandResultSuccess, cmd) =>
            this.state.addHistory(cmd)
            r
          case Some(r, _) =>
            r
          case None => TempuCommandResultFailure(s"illegal command: ${cmdStr}. " + helpStr())
        }
    }
  }
}
