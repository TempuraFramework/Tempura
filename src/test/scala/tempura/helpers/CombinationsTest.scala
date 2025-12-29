package tempura.helpers

import org.scalatest.funsuite.AnyFunSuite

class CombinationsTest extends AnyFunSuite {

  test("combinations of size 2 from list of 3") {
    val result = Utils.combinations(List(1, 2, 3), 2)
    assert(result.toSet == Set(List(1, 2), List(1, 3), List(2, 3)))
    assert(result.length == 3)
  }

  test("combinations of size 3 from list of 4") {
    val result = Utils.combinations(List('a', 'b', 'c', 'd'), 3)
    assert(result.length == 4)
    assert(result.toSet == Set(
      List('a', 'b', 'c'),
      List('a', 'b', 'd'),
      List('a', 'c', 'd'),
      List('b', 'c', 'd')
    ))
  }

  test("combinations of size 0 returns single empty list") {
    val result = Utils.combinations(List(1, 2, 3), 0)
    assert(result == List(List()))
  }

  test("combinations where k > n returns empty list") {
    val result = Utils.combinations(List(1, 2, 3), 4)
    assert(result == List())
  }

  test("combinations of size n from list of n returns single full list") {
    val result = Utils.combinations(List(1, 2, 3), 3)
    assert(result == List(List(1, 2, 3)))
  }

  test("combinations from empty list with k=0") {
    val result = Utils.combinations(List(), 0)
    assert(result == List(List()))
  }

  test("combinations from empty list with k>0") {
    val result = Utils.combinations(List(), 1)
    assert(result == List())
  }

  test("combinations preserves order within each subset") {
    val result = Utils.combinations(List(1, 2, 3, 4), 2)
    // All sublists should maintain the original order
    result.foreach { sublist =>
      assert(sublist == sublist.sorted)
    }
  }

  test("combinations count matches binomial coefficient C(5,2) = 10") {
    val result = Utils.combinations(List(1, 2, 3, 4, 5), 2)
    assert(result.length == 10)
  }

  test("combinations count matches binomial coefficient C(6,3) = 20") {
    val result = Utils.combinations(List('a', 'b', 'c', 'd', 'e', 'f'), 3)
    assert(result.length == 20)
  }

  test("combinations of size 1 returns each element as singleton list") {
    val result = Utils.combinations(List(10, 20, 30), 1)
    assert(result.toSet == Set(List(10), List(20), List(30)))
  }

  test("combinations with strings") {
    val result = Utils.combinations(List("alpha", "beta", "gamma"), 2)
    assert(result.length == 3)
    assert(result.toSet == Set(
      List("alpha", "beta"),
      List("alpha", "gamma"),
      List("beta", "gamma")
    ))
  }
}
