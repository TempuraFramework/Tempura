package org.abstractpredicates.parsing.printers

import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.helpers.Transforms.EnvTransform
import org.abstractpredicates.transitions.TransitionSystem

object VMTPrinter extends EnvTransform[TransitionSystem, String] {


  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(a: TransitionSystem): Either[String, String] = ???
}
