package org.abstractpredicates.repl


class TempuScriptState[T] {
  private var history = List.empty[TempuCommand[T]]

  def addHistory(t: TempuCommand[T]): Unit =
    history = t :: history

  def getHistory: List[TempuCommand[T]] = history

  def clearHistory(): Unit =
    history = List.empty[TempuCommand[T]]

  def vectorized: IndexedSeq[String] =
    getHistory.map(_.toString).toVector
}