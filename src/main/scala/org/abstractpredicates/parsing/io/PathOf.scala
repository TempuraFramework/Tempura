package org.abstractpredicates.parsing.io

import java.nio.file.Path
import org.abstractpredicates.helpers.TempuraTransform
import org.abstractpredicates.expression.Core

class PathOf extends TempuraTransform[String, Path] {
  override def apply(te: Core.TypeEnv, ie: Core.InterpEnv)(a: String) : Either[String, Path] = {
    try 
      Right(Path.of(a))
    catch
      case e => Left(e.toString)
  }
}
