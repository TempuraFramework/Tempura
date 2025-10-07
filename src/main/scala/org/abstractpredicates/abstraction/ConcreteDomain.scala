package org.abstractpredicates.abstraction

import algebra.lattice.BoundedLattice

//
// Similarly concrete domains are also typeclasses
//
trait ConcreteDomain[T] extends BoundedLattice[T]
