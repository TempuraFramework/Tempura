package tempura.parsing.io

import tempura.cozy.AutoRegister

import java.nio.file.Path
import java.nio.file.Files
import scala.io.Source
import scala.util.Using
import tempura.cozy.Transforms.*

import scala.reflect.ClassTag

@AutoRegister("read-string")
object StringReader extends Transform[Tuple1[Path], Tuple1[String]] {

  override def apply(arg: Tuple1[Path]): Either[String, Tuple1[String]] = {
    val path = arg._1
    if !(Files.exists(path)) then
      Left(s"File does not exist: $path")
    else
      Right(Using.resource(Source.fromFile(path.toString)) { source =>
        Tuple1(source.mkString)
      })

  }
}