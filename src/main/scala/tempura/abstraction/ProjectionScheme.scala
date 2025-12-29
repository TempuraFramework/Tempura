package tempura.abstraction

import tempura.expression.Core

trait ProjectionScheme[A] {
  def apply(a: A): Map[String, Core.BoxedSort]
}
