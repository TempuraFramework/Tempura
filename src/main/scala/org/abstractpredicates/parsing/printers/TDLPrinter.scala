package org.abstractpredicates.parsing.printers

import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.helpers.Transforms.EnvTransform
import org.abstractpredicates.transitions.TransitionSystem

import scala.reflect.ClassTag

object TDLPrinter extends EnvTransform[TransitionSystem, String](using summon[ClassTag[TransitionSystem]], summon[ClassTag[String]]) {

  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(a: TransitionSystem): Either[String, String] = ???
}
