package org.abstractpredicates.parsing.io

import scala.io.Source
import org.abstractpredicates.parsing.ast.{ParseTree, VMTParser}
import org.abstractpredicates.parsing.parsers.StringToSExprParser
import org.abstractpredicates.transitions.PreTransitionSystem

import scala.util.Using
import cats.implicits.*

import java.nio.file.{Files, Paths}

class TransitionSystemReader(path: String) {

  def readString: Either[String, String] =
    if !path.endsWith(".vmt") then
      Left(s"Expected a .vmt file, got: $path")
    else {
      if !(Files.exists(Paths.get(path))) then
        Left(s"File does not exist: $path")
      else
        Right(Using.resource(Source.fromFile(Paths.get(path).toString)) { source =>
          source.mkString
        })
    }


  def readSexpr: Either[String, List[ParseTree]] = {
    this.readString match {
      case Right(inputString) =>
        StringToSExprParser.setInput(inputString)
        StringToSExprParser.transformInput match {
          case Some(t) => Right(t)
          case None => Left("readSexpr: Failed to parse S-expressions from input string.")
        }
      case Left(reason) => Left(reason)
    }
  }

  def readVMT: Either[String, PreTransitionSystem] = {
    val pts = PreTransitionSystem()
    readSexpr match {
      case Right(sexprs) =>
        sexprs.traverse(
          sexpr =>
            println("\nparsing sexpr: " + sexpr.toString)
            VMTParser.parse(pts)(sexpr) match {
              case Right(answer) => println(" ... [ok]\n"); Right(answer)
              case Left(reason) => println(" ... [failure]\n"); Left(reason)
            }
        ) match {
          case Right(_) => Right(pts)
          case Left(reason) => Left(s"readVMT: Failed parsing transition system from VMT file ${path}. Error: ${reason}")
        }
      case Left(reason) =>
        Left(reason)
    }
  }
}
