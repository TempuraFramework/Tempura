package org.abstractpredicates.abstraction

import algebra.Semigroup

//
// R is an idempotent semiring
// G is a semigroup
// op: R x G -> G is an action
trait SemiModule[R, G] extends IdempotentSemiring[R], Semigroup[G] {

  def combine(x: G, y: G): G

  def plus(x: R, y: R): R

  def zero: R

  def one: R

  def times(x: R, y: R): R

  def action(r: R, g: G): G

}
