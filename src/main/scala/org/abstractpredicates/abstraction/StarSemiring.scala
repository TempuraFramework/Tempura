package org.abstractpredicates.abstraction

trait StarSemiring[T] extends IdempotentSemiring[T] {
  def star(t: T) : T 
}
