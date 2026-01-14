package tempura.abstraction

import org.scalatest.funsuite.AnyFunSuite
import tempura.expression.Core
import tempura.parsing.io.TDLReader

class ConcretizerTest extends AnyFunSuite {

  test("ranking_infer1") {
    val (typeEnv, interpEnv) = (Core.emptyTypeEnv, Core.emptyInterpEnv)
    TDLReader(Tuple1("examples/ranking_infer1.unconcretized.tdl")) match {
      case Right(Tuple1(ts)) =>
        ???
      case Left(msg) => 
        println("err " + msg)
        assert(false)
    }
        
  } 
}
