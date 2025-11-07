package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Syntax.*
import org.scalatest.funsuite.AnyFunSuite

import scala.List
import scala.language.postfixOps

class SyntaxTests extends AnyFunSuite {

  test("boolean syntax sugar") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val x = interpEnv | ("x", Core.boolSort)
    val y = interpEnv | ("y", Core.boolSort)
    val z = interpEnv | ("z", Core.boolSort)

    assert(/\(x, y) == Core.mkAnd(List(x, y)))
    assert(\/(y, x) == Core.mkOr(List(y, x)))
    assert((x /\ y) == Core.mkAnd(List(x, y)))
    assert((x \/ y) == Core.mkOr(List(x, y)))
    assert(x /\ y /\ z == Core.mkAnd(List(x, Core.mkAnd(List(y, z)))))

  }

  test("array syntax sugar") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val x = interpEnv.newVar("x", Core.boolSort)
    val arr = interpEnv.newVar("arr", Core.arraySort(Core.boolSort, Core.boolSort))
    val z = interpEnv.newVar("z", Core.boolSort)
    assert((arr@<x>) == Core.mkSelect(arr, x))
    assert((arr@<x>=z) == Core.mkStore(arr, x, z))
  }
}
