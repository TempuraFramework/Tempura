package org.abstractpredicates.parsing.io

import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.Files
import org.abstractpredicates.helpers.TempuraTransform
import org.abstractpredicates.expression.Core
import scala.util.Using
import scala.io.Source
import org.abstractpredicates.parsing.sexpr.{ParseTree, StringToSExprParser, VMTParser}
import org.abstractpredicates.transitions.PreTransitionSystem
import org.abstractpredicates.expression.Core
import scala.util.Using
import cats.implicits.*


class StringReader extends TempuraTransform[Path, String] {
  private var suff: Option[String] = None

  def this(suffix: String) = {
    this()
    suff = Some(suffix)
  }

  override def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(path: Path): Either[String, String] = {
    suff match {
      case Some(suffix) =>
        if !path.endsWith(suffix.toString) then
          Left(s"Expected a .vmt file, got: $path")
        else {
          if !(Files.exists(path)) then
            Left(s"File does not exist: $path")
          else
            Right(Using.resource(Source.fromFile(path.toString)) { source =>
              source.mkString
            })
        }
      case None =>
        if !(Files.exists(path)) then
          Left(s"File does not exist: $path")
        else
          Right(Using.resource(Source.fromFile(path.toString)) { source =>
            source.mkString
          })

    }
  }


}