package org.abstractpredicates.helpers

import org.abstractpredicates.expression.Core

trait TempuraTransform[A, B] {
  self =>
  def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(a: A): Either[String, B]

  def compose[C](parser: TempuraTransform[B, C]): TempuraTransform[A, C] =
    new TempuraTransform[A, C] {
      override def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(a: A): Either[String, C] = {
        self.apply(typeEnv, interpEnv)(a).flatMap(parser.apply(typeEnv, interpEnv)(_))
      }
    }
}