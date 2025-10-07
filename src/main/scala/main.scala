import de.uni_freiburg.informatik.ultimate.logic.{Logics, Sort, TermVariable}
import de.uni_freiburg.informatik.ultimate
import org.abstractpredicates.expression.Core.{ArraySort, BoolSort, NumericSort, Sort}
import org.abstractpredicates.parsing.ast.ParseTree.INode
import org.abstractpredicates.parsing.ast.VMTParser
import org.abstractpredicates.transitions.TransitionSystem
import org.abstractpredicates.smt.Z3Solver

import scala.quoted.Quotes
import scala.io.StdIn.readLine

object main {

  import org.abstractpredicates.expression._
  import Core.Expr
  import org.abstractpredicates.parsing.parsers.StringToSExprParser
  import org.abstractpredicates.repl.TempuScriptMain

  @main def hello() : Int =
    println(" *** starting TempuScript ***")
    //SmtInterpolSolver.init()
    TempuScriptMain.configure()
    //print("---test---")
    //val x = SmtInterpolSolver.solver.variable("x", SmtInterpolSolver.solver.sort("Bool"))
    //val z = SmtInterpolSolver.solver.quantifier(0, Array(x), SmtInterpolSolver.solver.term("and", x, SmtInterpolSolver.solver.term("true")))
    //print(z)
    //print("------")
    //0
    val (code, msg) = TempuScriptMain.run()
    println(msg)
    code
  /*
    val envM: Map[Expr[_], _] = Map(
      Expr.VarBool("a") -> BFalse,
      Expr.VarBool("b") -> BFalse
    )
    val env = Registry.Env(envM)
    val expr =
      Expr.App(
        Expr.Fun(x =>
          Expr.Or(x,
            Expr.And(Expr.Or(Expr.VarBool("a"), Expr.VarBool("b")), Expr.ConstBool(BTrue)))), Expr.ConstBool(BFalse))
    var v = new Visitor()
    println(v.eval(env)(expr))
  */
 /*   println("-----")
    SmtInterpolSolver.solver.setOption(":produce-proofs", true)
    SmtInterpolSolver.solver.setOption(":produce-interpolants", true)
    SmtInterpolSolver.solver.setLogic(Logics.QF_UFLIA)
    SmtInterpolSolver.solver.declareFun("x", new Array[ultimate.logic.Sort](0), SmtInterpolSolver.solver.sort("Int"))
    println(SmtInterpolSolver.solver.checkSat())
    println("SMTInterpol Limit: " + SmtInterpolSolver)
    println("------")
*/

//    val m = Map[String, Sort[_]](("ABCDE", NumericSort.SmallIntegral(3)), ("efgh", BoolSort.BTrue),
 //     ("xxx", ArraySort[BoolSort, UnInterpretedFunctionSort[BoolSort, BoolSort]]("arrSort", (x => ???)))
  //    )

    //println(ParseUtils.helperT[NumericSortV, NumericSortV]()//(NumericSortV.SmallIntegral(3)))
  //  var d = "xxx"
   // test(m, d) //"ABCDE")

    //println("-----")
    //var x = "(declare-fun\n\n\n |__loc:y| () time)\n(declare-fun\n |a| () b)"//
    //var x = scala.io.Source.fromFile("/home/rjf//Projects/ivy/test/ranking_infer1.vmt").mkString

    //var x = "(define-fun |.q1.receiving.value| () time (! q1.receiving.value :next new_q1.receiving.value))"
    // var x = "(declare-sort time 0)\n(declare-sort index 0)\n(declare-fun new_q1.trying.now () Bool)\n(declare-fun new_q1.receiving.value () time)\n(declare-fun time.succ (time time) Bool)\n(declare-fun |<:index:index| (index index) Bool)\n(declare-fun q1.receiving.value () time)\n(declare-fun |0:time| () time)\n(declare-fun q1.pending () (Array time Bool))\n(declare-fun |0:index| () index)\n(declare-fun __ts0__m_q1.receiving.now () Bool)\n(declare-fun |__fml:x| () time)\n(declare-fun |__new_fml:val| () time)\n(declare-fun |<:time:time| (time time) Bool)\n(declare-fun __ts0_b () Bool)\n(declare-fun q1.receiving.now () Bool)\n(declare-fun |__ts0__new_fml:val| () time)\n(declare-fun __ts0_a () Bool)\n(declare-fun __m_.r () Bool)\n(declare-fun new_q1.sending.value () time)\n(declare-fun __m_q1.trying.now () Bool)\n(declare-fun q1.sending.value () time)\n(declare-fun new_q1.pending () (Array time Bool))\n(declare-fun new_q1.receiving.now () Bool)\n(declare-fun new_q1.sending.now () Bool)\n(declare-fun __m_.r_a () Bool)\n(declare-fun .r () Bool)\n(declare-fun __m_q1.sending.now () Bool)\n(declare-fun q1.sending.now () Bool)\n(declare-fun new_.r () Bool)\n(declare-fun |__loc:y| () time)\n(declare-fun index.succ (index index) Bool)\n(declare-fun q1.trying.now () Bool)\n(define-fun .q1.trying.now () Bool (! q1.trying.now :next new_q1.trying.now))"

    //var x = "(declare-fun test () Bool)"//"(Array bool (Array (time idx) (Array Int Bool)))"
    //var x = "(declare-fun |<:index:index| (index index) Bool)"
    //var x = "(define-fun .q1.trying.now () Bool (! q1.trying.now :next new_q1.trying.now))"
    //var x = "(define-fun .__fmlx () time (! |__fml:x| :next new___fmlx))"
    //var x = "(define-fun .q1.recv () Bool (! q1.recv :action 0))"
    //var x = "(declare-fun new___ts0_b () time)"

  //  StringToSExprParser.setInput(x)
  //  val y = StringToSExprParser.transformInput
  //  println(y)
  //  y match {
  //    case Some(t) =>
  //      println(VMTParser.parse(Core.emptyTypeEnv, Core.emptyInterpEnv)(INode(t)))
  //    case None =>
  //      println("error: y cannot be parsed")
  //
  //  }

  //  println("******************")

  //  Core.ArraySort[Core.BoolSort, Core.BoolSort](Core.BoolSort(), Core.BoolSort()).ct.unapply(
  //    Core.ArraySort[Core.NumericSort, Core.BoolSort](Core.NumericSort(), Core.BoolSort())) match {
  //    case Some(b) =>
  //      println("unapply success: " + b.toString)
  //    case _ =>
  //      println("unapply failure")
  //  }
  //
  //  println(
  //    Core.ArraySort[Core.BoolSort, ArraySort[Core.BoolSort, Core.NumericSort]](Core.BoolSort(), Core.ArraySort[Core.BoolSort, Core.NumericSort](Core.BoolSort(), Core.NumericSort()))
  //      ==
  //    Core.ArraySort[Core.BoolSort, ArraySort[Core.BoolSort, Core.NumericSort]](Core.BoolSort(), Core.ArraySort[Core.BoolSort, Core.NumericSort](Core.BoolSort(), Core.NumericSort())))
  //  println(
  //    Core.ArraySort[Core.BoolSort, ArraySort[Core.BoolSort, Core.BoolSort]](Core.BoolSort(), Core.ArraySort[Core.BoolSort, Core.BoolSort](Core.BoolSort(), Core.BoolSort()))
  //      ==
  //      Core.ArraySort[Core.BoolSort, ArraySort[Core.BoolSort, Core.NumericSort]](Core.BoolSort(), Core.ArraySort[Core.BoolSort, Core.NumericSort](Core.BoolSort(), Core.NumericSort())))
  //
  //
  //  println("Z3-Turnkey Info: Version " + Z3Solver.version)

  //println("Hello, World")
  // val x = SExprParser.atom.parseAll("\"\\\"")
  //val x = StringToSExprParser.atom.parseAll("-uW,cRt.r")
  //println(x)
  //println("\\")
  //print(MyParser.expr.parseAll("(12345 + -123)"))
}