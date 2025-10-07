package org.abstractpredicates.abstraction

import algebra.lattice.Logic
import algebra.lattice.BoundedLattice

// Abstract domains are implemented as type classes.
// To implement a new abstract domain for a class T,
// use the given ... syntax to extend it with
// appropriate abstract domain operations.
trait AbstractDomain[T] extends BoundedLattice[T] {

  override def join(lhs: T, rhs: T): T

  override def meet(lhs: T, rhs: T): T

  // Widening operator for ensuring termination
  def widen(x: T, y: T): T = join(x, y)

  // Narrowing operator for precision refinement
  def narrow(x: T, y: T): T = meet(x, y)

}
