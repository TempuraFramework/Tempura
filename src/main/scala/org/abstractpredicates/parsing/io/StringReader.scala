package org.abstractpredicates.parsing.io

import java.nio.file.Path
import java.nio.file.Files
import scala.io.Source
import scala.util.Using
import org.abstractpredicates.helpers.Transforms.BasicTransform

import scala.reflect.ClassTag

object StringReader extends BasicTransform[Path, String](using summon[ClassTag[Path]], summon[ClassTag[String]]) {

  override def apply(path: Path): Either[String, String] = {
    if !(Files.exists(path)) then
      Left(s"File does not exist: $path")
    else
      Right(Using.resource(Source.fromFile(path.toString)) { source =>
        source.mkString
      })

  }
}