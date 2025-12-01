package org.abstractpredicates.parsing

import org.abstractpredicates.expression.Core
import org.abstractpredicates.parsing.ast.{ParseTree, VMTParser}
import org.abstractpredicates.parsing.parsers.StringToSExprParser
import org.abstractpredicates.transitions.PreTransitionSystem
import org.scalatest.funsuite.AnyFunSuite

class VMTParserTests extends AnyFunSuite {

  private def sexprs(s: String) : List[ParseTree] = {
    StringToSExprParser.setInput(s)
    StringToSExprParser.transformInput.get
  }

  test("parse declare-fun expression with empty domain ")  {
    val pts = PreTransitionSystem()
    val s = "(declare-fun x () Int)"
    sexprs(s) foreach {
      x =>
        println(s"parsing ${x}: ")
        VMTParser.parse(pts)(x) match {
          case Right(answer) => println(answer);
            val xFun = answer.getInterpEnv("x").get
            print(s"x = ${xFun}")
            assert(xFun.e == Core.Var("x", Core.NumericSort()))
          case Left(reason) => println(reason); assert(false)
        }
    }
  }

  test("parse declare-fun expression with type Bool->Bool->Int ") {
    val pts = PreTransitionSystem()
    val s = "(declare-fun x (Bool Bool) Int)"
    sexprs(s) foreach {
      x =>
        println(s"parsing ${x}: ")
        VMTParser.parse(pts)(x) match {
          case Right(answer) =>
            println(answer)
            val xFun = answer.getInterpEnv("x").get
            print(s"x = ${xFun.toString}")
            assert(xFun.e == Core.Var("x", Core.funSort(List(Core.BoolSort(), Core.BoolSort()),Core.NumericSort() )))
            assert(true)
          case Left(reason) => println(reason); assert(false)
        }
    }
  }

  test("parse declare-fun expression with type (Array Bool Int)->Bool->Int ") {
    val pts = PreTransitionSystem()
    val s = "(declare-fun x ((Array Bool Int) Bool) Int)"
    sexprs(s) foreach {
      x =>
        println(s"parsing ${x}: ")
        VMTParser.parse(pts)(x) match {
          case Right(answer) => println(answer)
            val xFun = answer.getInterpEnv("x").get
            print(s"x = ${xFun.toString}")
            assert(xFun.e == Core.Var("x", Core.funSort(List(Core.ArraySort(Core.BoolSort(), 
              Core.NumericSort()), Core.BoolSort()),Core.NumericSort() )))
            assert(true)
          case Left(reason) => println(reason); assert(false)
        }
    }
  }


  test("parse init condition") {
    val pts = PreTransitionSystem()
    val init = "(define-fun init () Bool (! true :init true))"
    sexprs(init) foreach {
      x =>
        println(s"parsing ${x}: ")
        VMTParser.parse(pts)(x) match {
          case Right(answer) => println(answer)
            assert(true)
          case Left(reason) => println(reason); assert(false)
        }
    }
  }

}
