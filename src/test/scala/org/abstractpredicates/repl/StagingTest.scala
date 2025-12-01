package org.abstractpredicates.repl

import org.scalatest.funsuite.AnyFunSuite

class StagingTest extends AnyFunSuite {

  test("test runtime staging") {
    import scala.quoted.*

    // make available the necessary compiler for runtime code generation
    given staging.Compiler = staging.Compiler.make(getClass.getClassLoader)


    def unrolledPowerCode(x: Expr[Double], n: Int)(using Quotes): Expr[Double] =
      if n == 0 then
        '{ 1.0 }
      else if n == 1 then
        x
      else
        '{ $x * ${ unrolledPowerCode(x, n - 1) } }

    val power3: Double => Double = staging.run {
      val stagedPower3: Expr[Double => Double] =
        '{ (x: Double) => ${ unrolledPowerCode('x, 3) } }
      println(stagedPower3.show) // Prints "((x: scala.Double) => x.*(x.*(x)))"
      stagedPower3
    }

    println("result = " + power3.apply(2.0)) // Returns 8.0
  }

}
