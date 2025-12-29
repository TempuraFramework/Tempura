package tempura.parsing.io

import scala.io.Source

import scala.util.Using
import cats.implicits.*
import tempura.cozy.Transforms.*
import tempura.expression.Core
import tempura.parsing.sexpr.{ParseTree, StringToSExprParser, TDLParser, VMTParser}
import tempura.transitions.{TransitionSystem, TransitionSystemBuffer}

import java.nio.file.{Files, Paths}
import scala.reflect.ClassTag

object TDLReader extends Transform[Tuple1[String], Tuple1[TransitionSystem]] {

  override def apply(arg: Tuple1[String]): Either[String, Tuple1[TransitionSystem]] = {
    val pipeline = PathOf *: StringReader *: StringToSExprParser *: EmptyTuple
    val result: Either[String, Tuple1[List[ParseTree]]] = compose(arg, pipeline)
    result match {
      case Right(Tuple1(parsed)) =>
        val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
        TDLParser((typeEnv, interpEnv, parsed))
      case e => Left(s"err: TDLReader: Expected List of ParseTree objects but got ${e}")
    }
  }
  

}
