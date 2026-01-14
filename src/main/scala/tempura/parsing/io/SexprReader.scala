package tempura.parsing.io

import tempura.cozy.AutoRegister
import tempura.cozy.Transforms.*
import tempura.parsing.sexpr.*

import java.nio.file.{Files, Path}
import scala.reflect.ClassTag


@AutoRegister("read-sexpr")
object SexprReader extends Transform[Tuple1[String], Tuple1[List[ParseTree]]] {

  override def apply(a: Tuple1[String]): Either[String, Tuple1[List[ParseTree]]] = {
    val pipeline = PathOf *: StringReader *: StringToSExprParser *: EmptyTuple
    val result : Either[String, Tuple1[List[ParseTree]]] = compose(a, pipeline)
    result match {
      case Right(t) => Right(t)
      case Left(r) => Left(r)
    }
  }


}