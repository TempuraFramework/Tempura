package org.abstractpredicates.parsing

import org.abstractpredicates.parsing.io.TransitionSystemReader
import org.abstractpredicates.parsing.parsers.StringToSExprParser
import org.scalatest.funsuite.AnyFunSuite

class ParserTests2 extends AnyFunSuite {

  private final val test0 = "(declare-sort time 0)\n(declare-sort index 0)\n(declare-fun new_q1.trying.now () Bool)\n(declare-fun |__ts0__new_fml:val| () time)\n(declare-fun |__loc:y| () time)\n(declare-fun new_q1.pending () (Array time Bool))\n(declare-fun q1.receiving.value () time)\n(declare-fun |0:index| () index)\n(declare-fun |__fml:x| () time)\n(declare-fun new_.r () Bool)\n(declare-fun __m_.r_a () Bool)\n(declare-fun __ts0_b () Bool)\n(declare-fun time.succ (time time) Bool)\n(declare-fun new_q1.sending.now () Bool)\n(declare-fun q1.test_fun () (Array time (Array time Bool)))\n(declare-fun q1.sending.value () time)\n(declare-fun __ts0__m_q1.receiving.now () Bool)\n(declare-fun new_q1.test_fun () (Array time (Array time Bool)))\n(declare-fun index.succ (index index) Bool)\n(declare-fun __ts0_a () Bool)\n(declare-fun q1.sending.now () Bool)\n(declare-fun q1.receiving.now () Bool)\n(declare-fun __m_q1.trying.now () Bool)\n(declare-fun |<:time:time| (time time) Bool)\n(declare-fun |<:index:index| (index index) Bool)\n(declare-fun |0:time| () time)\n(declare-fun q1.pending () (Array time Bool))\n(declare-fun q1.trying.now () Bool)\n(declare-fun __m_q1.sending.now () Bool)\n(declare-fun new_q1.sending.value () time)\n(declare-fun __m_.r () Bool)\n(declare-fun new_q1.receiving.now () Bool)\n(declare-fun |__new_fml:val| () time)\n(declare-fun new_q1.receiving.value () time)\n(declare-fun .r () Bool)\n(define-fun .q1.trying.now () Bool (! q1.trying.now :next new_q1.trying.now))\n(declare-fun new___ts0__new_fmlval () time)\n(define-fun .__ts0__new_fmlval () time (! |__ts0__new_fml:val| :next new___ts0__new_fmlval))\n(declare-fun new___locy () time)\n(define-fun .__locy () time (! |__loc:y| :next new___locy))\n(define-fun .q1.pending () (Array time Bool) (! q1.pending :next new_q1.pending))\n(declare-fun new___fmlx () time)\n(define-fun .__fmlx () time (! |__fml:x| :next new___fmlx))\n(define-fun ..r () Bool (! .r :next new_.r))\n(declare-fun new___m_.r_a () Bool)\n(define-fun .__m_.r_a () Bool (! __m_.r_a :next new___m_.r_a))\n(declare-fun new___ts0_b () Bool)\n(define-fun .__ts0_b () Bool (! __ts0_b :next new___ts0_b))\n(define-fun .q1.sending.now () Bool (! q1.sending.now :next new_q1.sending.now))\n(declare-fun new___ts0__m_q1.receiving.now () Bool)\n(define-fun .__ts0__m_q1.receiving.now () Bool (! __ts0__m_q1.receiving.now :next new___ts0__m_q1.receiving.now))\n(define-fun .q1.test_fun () (Array time (Array time Bool)) (! q1.test_fun :next new_q1.test_fun))\n(declare-fun new___ts0_a () Bool)\n(define-fun .__ts0_a () Bool (! __ts0_a :next new___ts0_a))\n(declare-fun new___m_q1.trying.now () Bool)\n(define-fun .__m_q1.trying.now () Bool (! __m_q1.trying.now :next new___m_q1.trying.now))\n(declare-fun new___m_q1.sending.now () Bool)\n(define-fun .__m_q1.sending.now () Bool (! __m_q1.sending.now :next new___m_q1.sending.now))\n(define-fun .q1.sending.value () time (! q1.sending.value :next new_q1.sending.value))\n(declare-fun new___m_.r () Bool)\n(define-fun .__m_.r () Bool (! __m_.r :next new___m_.r))\n(define-fun .q1.receiving.now () Bool (! q1.receiving.now :next new_q1.receiving.now))\n(declare-fun new___new_fmlval () time)\n(define-fun .__new_fmlval () time (! |__new_fml:val| :next new___new_fmlval))\n(define-fun .q1.receiving.value () time (! q1.receiving.value :next new_q1.receiving.value))\n(declare-fun _idle () Bool)\n(define-fun ._idle () Bool (! _idle :action 0))\n(declare-fun q1.recv () Bool)\n(define-fun .q1.recv () Bool (! q1.recv :action 0))\n(declare-fun q1.send () Bool)\n(define-fun .q1.send () Bool (! q1.send :action 0))\n(define-fun init () Bool (! (and (not .r)\n     (= q1.pending ((as const (Array time Bool)) false))\n     (= q1.test_fun\n        ((as const (Array time (Array time Bool)))\n          ((as const (Array time Bool)) false)))\n     (not q1.sending.now)\n     (not q1.trying.now)\n     (not q1.receiving.now)) :init true))\n(define-fun trans () Bool (! (and (=> _idle (and (not new_.r)\n     (= q1.trying.now new_q1.trying.now)\n     (= q1.pending new_q1.pending)\n     (= q1.receiving.value new_q1.receiving.value)\n     (= q1.receiving.now new_q1.receiving.now)\n     (= q1.test_fun new_q1.test_fun)\n     (= q1.sending.value new_q1.sending.value)\n     (= q1.sending.now new_q1.sending.now)))\n(=> q1.recv (let ((a!1 (forall ((|V0:time| time))\n             (or (not __ts0_b) (not (select q1.pending |V0:time|))))))\n  (and (not __m_.r_a)\n       __m_q1.trying.now\n       (= __m_.r (or __m_.r_a __m_q1.trying.now))\n       (not new_q1.trying.now)\n       (= new_.r (or __m_.r new_q1.trying.now))\n       (= new_q1.pending\n          (ite __ts0_b q1.pending (store q1.pending |__loc:y| false)))\n       (= |__ts0__new_fml:val| |__loc:y|)\n       (= new_q1.receiving.value\n          (ite __ts0_b q1.receiving.value |__ts0__new_fml:val|))\n       __ts0__m_q1.receiving.now\n       (= new_q1.receiving.now (and __ts0_b q1.receiving.now))\n       (= q1.test_fun new_q1.test_fun)\n       (= q1.sending.value new_q1.sending.value)\n       (= q1.sending.now new_q1.sending.now)\n       (or __ts0_a __ts0_b)\n       (or (not __ts0_a) (select q1.pending |__loc:y|))\n       (forall ((|V0:time| time))\n         (let ((a!1 (not (and (select q1.pending |V0:time|)\n                              (or (= |V0:time| |__loc:y|)\n                                  (|<:time:time| |V0:time| |__loc:y|))\n                              (not (= |V0:time| |__loc:y|))))))\n           (or (not __ts0_a) a!1)))\n       a!1)))\n(=> q1.send (let ((a!1 (forall ((|T:time| time))\n             (or (not (select q1.pending |T:time|))\n                 (|<:time:time| |T:time| |__fml:x|)))))\n  (and (not new_.r)\n       (= new_q1.pending (store q1.pending |__fml:x| true))\n       (= new_q1.test_fun\n          (store q1.test_fun |__fml:x| ((as const (Array time Bool)) true)))\n       (= |__new_fml:val| |__fml:x|)\n       (= new_q1.sending.value |__new_fml:val|)\n       __m_q1.sending.now\n       (not new_q1.sending.now)\n       (= q1.trying.now new_q1.trying.now)\n       (= q1.receiving.value new_q1.receiving.value)\n       (= q1.receiving.now new_q1.receiving.now)\n       a!1)))\n(or _idle q1.recv q1.send)\n(or (not _idle) (not q1.recv))\n(or (not _idle) (not q1.send))\n(or (not q1.recv) (not q1.send))) :trans true))\n(assert (forall ((|X:index| index) (|Y:index| index) (|Z:index| index))\n  (let ((a!1 (and (|<:index:index| |X:index| |Z:index|)\n                  (not (and (|<:index:index| |X:index| |Y:index|)\n                            (|<:index:index| |Y:index| |Z:index|))))))\n    (or (not (index.succ |X:index| |Z:index|)) a!1))))\n(assert (forall ((|T:index| index) (|U:index| index) (|V:index| index))\n  (or (not (and (|<:index:index| |T:index| |U:index|)\n                (|<:index:index| |U:index| |V:index|)))\n      (|<:index:index| |T:index| |V:index|))))\n(assert (forall ((|T:index| index) (|U:index| index))\n  (not (and (|<:index:index| |T:index| |U:index|)\n            (|<:index:index| |U:index| |T:index|)))))\n(assert (forall ((|T:index| index) (|U:index| index))\n  (or (|<:index:index| |T:index| |U:index|)\n      (= |T:index| |U:index|)\n      (|<:index:index| |U:index| |T:index|))))\n(assert (forall ((|X:index| index))\n  (or (= |0:index| |X:index|) (|<:index:index| |0:index| |X:index|))))\n(assert (forall ((|X:time| time) (|Y:time| time) (|Z:time| time))\n  (let ((a!1 (and (|<:time:time| |X:time| |Z:time|)\n                  (not (and (|<:time:time| |X:time| |Y:time|)\n                            (|<:time:time| |Y:time| |Z:time|))))))\n    (or (not (time.succ |X:time| |Z:time|)) a!1))))\n(assert (forall ((|T:time| time) (|U:time| time) (|V:time| time))\n  (or (not (and (|<:time:time| |T:time| |U:time|)\n                (|<:time:time| |U:time| |V:time|)))\n      (|<:time:time| |T:time| |V:time|))))\n(assert (forall ((|T:time| time) (|U:time| time))\n  (not (and (|<:time:time| |T:time| |U:time|) (|<:time:time| |U:time| |T:time|)))))\n(assert (forall ((|T:time| time) (|U:time| time))\n  (or (|<:time:time| |T:time| |U:time|)\n      (= |T:time| |U:time|)\n      (|<:time:time| |U:time| |T:time|))))\n(assert (forall ((|X:time| time))\n  (or (= |0:time| |X:time|) (|<:time:time| |0:time| |X:time|))))\n(define-fun .p () Bool (! (and q1.sending.now (= q1.sending.value _X)) :react_p true))\n(define-fun .q () Bool (! (and q1.receiving.now (= q1.receiving.value _X)) :react_q true))\n(define-fun .r () Bool (! q1.trying.now :react_r true))\n"

  private def diffFast(s1: String, s2: String): IndexedSeq[String] = {
    val builder = Vector.newBuilder[String]

    def diff(short: String, long: String, status: String) = {
      builder.sizeHint(long.length)
      var i = 0

      while (i < short.length) {
        val x = s1.charAt(i)
        val y = s2.charAt(i)
        if (x != y) builder += s"$x != $y"
        i += 1
      }

      while (i < long.length) {
        val x = long.charAt(i)
        builder += s"$x is $status"
        i += 1
      }
    }

    if (s1.length <= s2.length) diff(s1, s2, "missing")
    else diff(s2, s1, "undefined")

    builder.result
  }

  test("read entire VMT file string to SExpr") {
    StringToSExprParser.setInput(test0)
    StringToSExprParser.transformInput match {
      case Some(x) =>
        println(s"successfully parsed: ${x}")
        assert(true)
      case None => assert(false)
    }
  }

  test("read entire VMT file string and compare it with test0") {
    val reader = TransitionSystemReader("examples/ranking_infer1.vmt")
    reader.readString match {
      case Right(inputString) =>
        println("Read input: " + inputString)
        if inputString != test0 then
          println(s"***** DIFF **** \n ${diffFast(inputString, test0)}\n")
        assert(inputString == test0)
      case Left(error) =>
        println(s"got error: ${error}")
        assert(false)
    }
  }

  test("read entire VMT file string and parse it into Sexpr") {
    val reader = TransitionSystemReader("examples/ranking_infer1.vmt")
    reader.readSexpr match {
      case Right(inputSExpr) =>
        println("Read input: " + inputSExpr)
        assert(true)
      case Left(error) =>
        println(s"got error: ${error}")
        assert(false)
    }
  }
  
  test("read entire VMT file string and parse it into PreTransitionSystem") {
    val reader = TransitionSystemReader("examples/ranking_infer1.vmt")
    reader.readVMT match {
      case Right(pts) =>
        println("read input: " + pts.toString)
        assert(true)
      case Left(error) =>
        println(s"got error: ${error}")
        assert(false)   
    }
  }
}
