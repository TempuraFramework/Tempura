package org.abstractpredicates.parsing.io

import scala.io.Source
import org.abstractpredicates.parsing.sexpr.{ParseTree, StringToSExprParser, TDLParser, VMTParser}
import org.abstractpredicates.transitions.{PreTransitionSystem, TransitionSystem}
import org.abstractpredicates.expression.Core

import scala.util.Using
import cats.implicits.*
import org.abstractpredicates.helpers.Transforms.*

import java.nio.file.{Files, Paths}
import scala.reflect.ClassTag

object TDLReader extends BasicTransform[String, TransitionSystem](using summon[ClassTag[String]], summon[ClassTag[TransitionSystem]]) {

  override def apply(a: String): Either[String, TransitionSystem] = {
    pipeline[String](List(PathOf.box, StringReader.box, StringToSExprParser.box))(a) flatMap {
      case (result: List[ParseTree]) =>
        val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
        TDLParser(typeEnv, interpEnv)(result)
    }
  }

}
