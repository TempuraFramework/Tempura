package tempura.helpers

import org.scalatest.funsuite.AnyFunSuite

class UtilsTest extends AnyFunSuite {

  test("sampleAll test") {
    val out = Utils.sampleAll(List("a", "b", "c"), 5)
    println(out.mkString("\n"))
  }

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
