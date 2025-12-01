package org.abstractpredicates.parsing

import org.abstractpredicates.parsing.sexpr.{ParseTree, ParseValue, StringToSExprParser}
import org.scalacheck.{Gen, Prop, Properties}
import org.scalacheck.Prop.{forAll, forAllNoShrink}


trait SExprGenerators {
  val charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-_!@#$%^&*:.,\\/"

  // yields set of legal terms
  val termGen: Gen[String] = for {
    len <- Gen.choose(10, 100)
    str <- Gen.listOfN(len, Gen.oneOf(charset))
  } yield str.mkString

  // yields set of separators
  val blanksGen : Gen[String] = for {
    len <- Gen.choose(10, 100)
    str <- Gen.listOfN(len, Gen.oneOf(" \n\t"))
  } yield str.mkString

  // yields double quoted strings
  val stringGen : Gen[String] = for {
    len <- Gen.choose(10, 100)
    str <- Gen.listOfN(len, Gen.asciiPrintableChar) map {
      _ map { // list of chars => list of strings
        c =>
          if c == '\"' || c == '\n' then "."
          else c.toString
      }
    }
  } yield str.mkString // **NOT** surrounded by "..."

  // yields numbers
  val numberGen : Gen[Int] = Gen.choose(-999999, 999999)

  // yields s-expression values
  val sexprValGen : Gen[ParseValue] = Gen.oneOf(
    termGen.map(ParseValue.PTerm(_)),
    stringGen.map(ParseValue.PString(_)),
    numberGen.map(ParseValue.PNumber(_))
  )

  def sizedSexprs(size: Int) : Gen[ParseTree] =
    if (size <= 0) {
      sexprValGen.map(ParseTree.Leaf(_)) // base case
    } else {
      val subtreeSize = size - 1
      val branchingFactor = Gen.choose(1, 10).sample.getOrElse(2)
      Gen.frequency(
        2 -> sexprValGen.map(ParseTree.Leaf(_)),
        1 -> Gen.listOfN(branchingFactor, sizedSexprs(subtreeSize)).map(ParseTree.INode(_))
      )
    }

  def sexprs: Gen[ParseTree] = Gen.sized({t => sizedSexprs(t) })
}


object TestSExprParser extends Properties("TestSExprParser") with SExprGenerators {

  property("testParsingTerms") = forAll(termGen) { (t: String) =>
    print("generated term: " + t + "\n")
    StringToSExprParser.term.parseAll(t) match {
      case Right(t) =>
        true
      case _ => false
    }
  }

  property("testParsingStrings") = forAll(stringGen) { (s: String) =>
    print("generated string: " + s + "\n")
    StringToSExprParser.stringVal.parseAll("\"" + s + "\"") match {
      case Right(t) =>
        true
      case a =>
        println("failed: " + a)
        false
    }
  }

  property("testParsingNumbers") = forAll(numberGen) { (n:Int) =>
    print("generated number: " + n + "\n")
    StringToSExprParser.number.parseAll(n.toString) match {
      case Right(t) =>
        true
      case a =>
        println("failed: " + a)
        false
    }
  }

  property("testSExprVals") = forAll(sexprValGen) {v =>
    println("SEXpr-Value: " + v.toString)
    val result = StringToSExprParser.atom.parseAll(v.toString())
    println("  ... result: " + result)
    result.getOrElse(false) match {
      case ParseTree.Leaf (ParseValue.PNumber(n)) =>
        println(" is Number " + n.toString)
        ParseValue.PNumber(n) == v
      case ParseTree.Leaf (ParseValue.PString(s)) => println(" is String " + s)
        if !(s == v.toString.slice(1, v.toString.length - 1)) then {
          println("Error: string inequality test failed!")
          println("string s : " + s)
          println("string v : " + v.toString.slice(1, v.toString.length - 1))
          println("")
          false
        } else
          true
      case ParseTree.Leaf (ParseValue.PTerm(t)) => println(" is Term " + t)
        ParseValue.PTerm(t) == v
      case _ =>
        println("Error: " + result)
        false
    }
  }

  property ("testSexprs") = forAll(sexprs) {v =>
    val result = StringToSExprParser.sexpr.parseAll(v.toString)
    println("Input: " + v.toString)
    println("Output:" + result.toString)
    result.getOrElse(false) match {
      case _ => true
    }
  }

}

