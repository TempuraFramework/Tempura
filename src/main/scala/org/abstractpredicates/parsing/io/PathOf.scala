package org.abstractpredicates.parsing.io

import java.nio.file.Path
import org.abstractpredicates.helpers.Transforms.BasicTransform
import scala.reflect.ClassTag

object PathOf extends BasicTransform[String, Path](using summon[ClassTag[String]], summon[ClassTag[Path]]) {
  override def apply(a: String): Either[String, Path] = {
    try
      Right(Path.of(a))
    catch
      case e => Left(e.toString)
  }
}
