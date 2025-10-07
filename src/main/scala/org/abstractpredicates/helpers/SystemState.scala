package org.abstractpredicates.helpers

import org.abstractpredicates.transitions.PreTransitionSystem

object SystemState {

  object Counter {
    private var counter = 0
    def next(): Int = {
      counter += 1
      counter
    }
  }

}
