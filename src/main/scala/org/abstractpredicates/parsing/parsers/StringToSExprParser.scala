package org.abstractpredicates.parsing.parsers

import cats.data.NonEmptyList
import cats.parse.Rfc5234.digit
import cats.parse.{Parser, Parser0, Rfc5234}
import org.abstractpredicates.parsing.ast.ParseTree.{INode, Leaf}
import org.abstractpredicates.parsing.ast.{ParseTree, ParseValue, Transformer}


object StringToSExprParser extends Transformer[String, List[ParseTree]] {
  val termSym: Parser[Char] = Parser.charIn("<=>+-/_!@#$%^&*:`~.,\\/")
  val blanks : Parser[Unit] = Parser.charIn(" \t\r\n").rep.void
  val lp0 : Parser[Unit] = Parser.char('(')
  val rp0 : Parser[Unit] = Parser.char(')')
  val lp: Parser[Unit] = lp0.surroundedBy(blanks) | lp0
  val rp: Parser[Unit] = rp0.surroundedBy(blanks) | rp0

  val term: Parser[ParseValue] = ((Rfc5234.alpha | Rfc5234.digit | termSym).rep map { t => ParseValue.PTerm(t.toList.mkString) }).withContext("term")
  val quotedTerm : Parser[ParseValue] =
    Parser.char('|') *> term <* Parser.char('|')

  //val stringVal : Parser[ParseValue] = (Rfc5234.dquote *> Parser.anyChar.rep0 <* Rfc5234.dquote) map { t => ParseValue.PString(t.mkString) }
  // TODO: we don't handle escaped strings like \"
  val unescapedChar: Parser[Char] =
    Parser.charWhere(c => c != '"').withContext("unescapedChar")
  val stringContent: Parser[String] =
    unescapedChar
      .rep.map(_.toList.mkString).withContext("stringContent")
  val stringVal: Parser[ParseValue] =
    ((Parser.char('"') *> stringContent <* Parser.char('"')) map { ParseValue.PString(_) }).withContext("stringVal")


  // numbers
  val digits : Parser[NonEmptyList[Char]] = digit.rep.surroundedBy(blanks) | digit.rep
  val negativeDigits : Parser[NonEmptyList[Char]] = Parser.char('-') *> digits
  val positiveNumber : Parser[ParseValue] = digits map { t => ParseValue.PNumber(t.toList.mkString.toInt) }
  val negativeNumber : Parser[ParseValue] = negativeDigits map { t => ParseValue.PNumber(("-" + t.toList.mkString).toInt) }
  val number : Parser[ParseValue] = positiveNumber | negativeNumber

  // booleans
  val boolTrue : Parser[ParseValue] = Parser.string("true") map { _ => ParseValue.PBool(true) }
  val boolFalse : Parser[ParseValue] = Parser.string("false") map { _ => ParseValue.PBool(false) }
  val atom: Parser[ParseTree] = {
    // XXX: -number vs. '-'-prefixed symbol induces an ambiguity; use backtracking to resolve this.
    ((number.backtrack.orElse(
      boolTrue.backtrack.orElse(
        boolFalse.backtrack.orElse(
          term
        )
      )
    ) | stringVal | term | quotedTerm) map { Leaf(_) }).withContext("atom")
  }

  // S-expressions
  lazy val sexpr: Parser[ParseTree] = Parser.defer {
    val list: Parser[ParseTree] =
      lp *>
      sexpr.repSep0(blanks).map(exprs => INode(exprs.toList))
      <* rp

    (atom | list)
      .withContext("sexpr")
  }

  lazy val sexprs : Parser0[List[ParseTree]] = Parser.defer0 {
    sexpr.repSep0(blanks).withContext("sexprS")
  }

  override def setInput(a: String) : Unit = {
    this.input = Some(a.strip())
  }

  override def transformInput: Option[List[ParseTree]] = {
    this.input match {
      case Some(a) =>
        this.sexprs.parseAll(a) match {
          case Left(_) =>
            println(this.sexpr.parseAll(a))
            None
          case Right(b) => Some(b)
        }
      case None => None
    }
  }

}
