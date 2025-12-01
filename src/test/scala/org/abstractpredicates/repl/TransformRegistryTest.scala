package org.abstractpredicates.repl

import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.helpers.TransformRegistry

class TransformRegistryTest extends AnyFunSuite {

  test("registry objects") {
    println(s"registry elements: (${TransformRegistry.getRegistry.size})")
    TransformRegistry.getRegistry.foreach(x =>
      println(s"registry element: ${x.toString}")
    )
  }
}
