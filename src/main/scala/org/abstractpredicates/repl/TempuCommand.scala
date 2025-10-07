package org.abstractpredicates.repl

import ammonite.terminal.DelegateFilter

enum TempuCommandResult(val s: String) {

  case TempuCommandResultSuccess(st: String) extends TempuCommandResult(st)

  case TempuCommandResultFailure(st: String) extends TempuCommandResult(st)

  case TempuCommandResultExit(st: String, val code: Int) extends TempuCommandResult(st)
  
  def getString : String = s
}


trait TempuCommand[T] {

  def getName : String

  def parseName(name: T) : Boolean

  def getDescription: String

  def apply(args: T*): TempuCommandResult

  def toString : String
}

given Ordering[TempuCommandResult] = Ordering.by(_.getString)
given Ordering[TempuCommand[?]] = Ordering.by(_.getName)