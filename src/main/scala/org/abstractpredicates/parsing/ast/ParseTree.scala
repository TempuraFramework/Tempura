package org.abstractpredicates.parsing.ast

//sealed trait Tree

enum ParseTree {
  case INode(children: List[ParseTree])
  case Leaf(value: ParseValue)


  // this composed with parsing of SEXPRs must be idempotent
  // XXX: the only problematic part is the printing of double-quotes
  // before a string value. When writing tests, need to ensure
  // we don't repeatedly double-quote a double-quoted string returned from here.
  override def toString: String =
    this match
      case Leaf(v) =>
        "(" + v.toString + ")"
      case INode(children) =>
        "(" + (children map {_.toString}).mkString(" ") + ")"
}
