package tempura.parsing.io

import tempura.cozy.AutoRegister
import tempura.cozy.Transforms.*
import tempura.expression.Core
import tempura.parsing.sexpr.{ParseTree, StringToSExprParser, VMTParser}
import tempura.transitions.TransitionSystem

import scala.reflect.ClassTag

@AutoRegister("read-vmt")
object VMTReader extends Transform[Tuple1[String], Tuple1[TransitionSystem]] {
  override def apply(a: Tuple1[String]): Either[String, Tuple1[TransitionSystem]] = {
    val pipeline = (PathOf, StringReader, StringToSExprParser)
    compose(a, pipeline) flatMap {
      case (result: List[ParseTree]) =>
        val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
        VMTParser((typeEnv, interpEnv, result))
    }
  }
}
