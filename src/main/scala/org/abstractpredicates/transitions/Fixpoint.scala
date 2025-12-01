package org.abstractpredicates.transitions

// Generic representation of a fixpoint approximator
// for a given transition system
trait Fixpoint {

  def explore(): Unit
}
