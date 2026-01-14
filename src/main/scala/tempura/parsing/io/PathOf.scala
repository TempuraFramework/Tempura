package tempura.parsing.io

import tempura.cozy.{AutoRegister, Transforms}

import java.nio.file.Path
import tempura.cozy.Transforms.*

import scala.reflect.ClassTag

@AutoRegister("path-of")
object PathOf extends Transform[Tuple1[String], Tuple1[Path]] {

  override def apply(args : Tuple1[String]): Either[String, Tuple1[Path]] = {
    try
      Right(Tuple1(Path.of(args._1)))
    catch
      case e => Left(e.toString)
  }
}
