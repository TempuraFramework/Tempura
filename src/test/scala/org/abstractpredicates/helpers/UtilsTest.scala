package org.abstractpredicates.helpers

import org.scalatest.funsuite.AnyFunSuite

class UtilsTest extends AnyFunSuite {

  test("product test") {
    val out = (Utils.cartesianProduct(
      List(
        List("x", "y"),
        List("z", "w"),
        List("0", "1", "2"),
        List("a", "b", "c", "d", "e")
      )
    ))
    println(out)
    assert(out.size == 2 * 2 * 3 * 5)
  }
}
