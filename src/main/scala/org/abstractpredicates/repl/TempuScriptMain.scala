package org.abstractpredicates.repl

import ammonite.terminal.filters.*
import GUILikeFilters.SelectionFilter
import ammonite.terminal.{Filter, Terminal}
import ammonite.terminal.LazyList.~:
import ammonite.terminal.TermState

import java.io.OutputStreamWriter
import scala.annotation.tailrec
import org.abstractpredicates.helpers.Utils.|>
import org.abstractpredicates.parsing.sexpr.{ParseTree, StringToSExprParser}
import org.abstractpredicates.repl.TempuCommandResult.TempuCommandResultExit

// The code below extends the Ammonite REPL code at
// https://github.com/com-lihaoyi/Ammonite/blob/main/terminal/src/test/scala/ammonite/terminal/TestMain.scala#L23


object TempuScriptMain {


  private val state: TempuScriptState[ParseTree] = TempuScriptState[ParseTree]()
  private val dispatcher = TempuCommandDispatcher[ParseTree](state,
    Set(CommonCommands.HistoryCommandStateful(state),
      CommonCommands.ExitCommand()))

  private val selection = GUILikeFilters.SelectionFilter(indent = 4)

  private def tabCompletionFilter(completions: List[String]) = Filter.partial {
    case TermState(9 ~: rest, buffer, cursor, _) =>
      val prefix = buffer.take(cursor).reverseIterator.takeWhile(_.isLetter).toList.reverse.mkString
      val startIdx = cursor - prefix.length

      val matches = completions.filter(_.startsWith(prefix))

      matches match {
        case Nil =>
          // No match, do nothing special
          TermState(rest, buffer, cursor)

        case onlyOne :: Nil =>
          // Single match: complete the word
          val newBuf = buffer.take(startIdx) ++ onlyOne.toVector ++ buffer.drop(cursor)
          val newCursor = startIdx + onlyOne.length
          TermState(rest, newBuf, newCursor)

        case many =>
          // Multiple matches: show completions (as a debug behavior, you could print to stderr or just no-op)
          println("\n" + many.mkString("  "))
          TermState(rest, buffer, cursor)
      }
  }


  def multilineFilter: Filter = Filter.partial {
    case TermState(13 ~: rest, b, c, _) if b.count(_ == '(') != b.count(_ == ')') =>
      BasicFilters.injectNewLine(b, c, rest)
  }

  val reader = new java.io.InputStreamReader(System.in)
  val cutPaste = ReadlineFilters.CutPasteFilter()

  def configure(): Unit = {
    System.setProperty("amm-sbt-build", "true")
  }

  def error(msg: String) = {
    println("\n" + Console.RED_B + Console.UNDERLINED + "Error:" + Console.RESET + " " + msg + "\n")
  }

  def success(msg: String) = {
    println("\n" + Console.GREEN_B + Console.UNDERLINED + "Output:" + Console.RESET + " " + msg + "\n")
  }

  // runs terminal and does not halt.
  @tailrec def run(): (Int, String) = {
    val historyFilter = new HistoryFilter(() => state.vectorized, fansi.Color.Blue)
    Terminal.readLine(
      "\n" + Console.BLUE_B + Console.BOLD + "=?> " + Console.RESET,
      reader,
      new OutputStreamWriter(System.out),
      Filter.merge(
        tabCompletionFilter(dispatcher.getCommands.map(x => x.getName).toList),
        UndoFilter(),
        cutPaste,
        historyFilter,
        multilineFilter,
        selection,
        BasicFilters.tabFilter(4),
        GUILikeFilters.altFilter,
        GUILikeFilters.fnFilter,
        ReadlineFilters.navFilter,
        //        Example multiline support by intercepting Enter key
        BasicFilters.all
        // tab-completion filter
      ),
      // Example displayTransform: underline all non-spaces
      displayTransform = (buffer, cursor) => {
        // underline all non-blank lines

        def hl(b: Vector[Char]): Vector[Char] = b.flatMap {
          case ' ' => " "
          case '\n' => "\n"
          case c => Console.UNDERLINED + c + Console.RESET
        }

        // and highlight the selection
        val ansiBuffer = fansi.Str(SeqCharSequence(hl(buffer)))
        val (newBuffer, cursorOffset) = SelectionFilter.mangleBuffer(
          selection,
          ansiBuffer,
          cursor,
          fansi.Reversed.On
        )
        val newNewBuffer = HistoryFilter.mangleBuffer(
          historyFilter,
          newBuffer,
          cursor,
          fansi.Color.Green
        )

        (newNewBuffer, cursorOffset)
      }
    ) match {
      case None =>
        (1, "Error processing Ammonite readline filters. Bye!")
      case Some(s) =>
        var (toExit, exitSt, exitCode) = (false, "", 0)
        StringToSExprParser(s) match {
          case Right(List(ParseTree.INode(parsedInput))) =>
            dispatcher.dispatch(parsedInput) match {
              case TempuCommandResult.TempuCommandResultSuccess(s) =>
                if s != "" then success(s)
              case TempuCommandResult.TempuCommandResultFailure(s) => error(s)
              case TempuCommandResultExit(st, code) =>
                toExit = true
                exitSt = st
                exitCode = code
            }
          case Right(List()) => ()
          case _ =>
            error(s"malformed input s-expression ${s}")
        }
        if !toExit then
          run()
        else
          (exitCode, exitSt)
    }
  }
}
