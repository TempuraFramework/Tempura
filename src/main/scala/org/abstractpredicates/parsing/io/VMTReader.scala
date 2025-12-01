package org.abstractpredicates.parsing.io

import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Transforms.{BasicTransform, pipeline}
import org.abstractpredicates.parsing.sexpr.{ParseTree, StringToSExprParser, VMTParser}
import org.abstractpredicates.transitions.TransitionSystem

import scala.reflect.ClassTag
given ClassTag[Int]    = ClassTag.Int
given ClassTag[String] = ClassTag(classOf[String])
object VMTReader extends BasicTransform[String, TransitionSystem](using summon[ClassTag[String]], summon[ClassTag[TransitionSystem]]) {

  override def apply(a: String): Either[String, TransitionSystem] = {
    pipeline[String](List(PathOf.box, StringReader.box, StringToSExprParser.box))(a) flatMap { 
      case (result: List[ParseTree]) =>
        val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
        VMTParser(typeEnv, interpEnv)(result)
    }
  }
}
