package tempura.expression.transforms

import tempura.expression.Syntax.*
import tempura.helpers.Utils.*
import tempura.transitions.TransitionFormula.Transition
import org.scalatest.funsuite.AnyFunSuite
import tempura.expression.Core
import tempura.parsing.io.TDLReader
import tempura.parsing.printers.TDLPrinter
import tempura.transitions.{TransformTransitionSystem, TransitionSystem}

class SortRenamerTest extends AnyFunSuite {

  test("test0") {
    val ts = TDLReader(Tuple1("examples/ranking_infer1.unconcretized.tdl")) match {
      case Right(Tuple1(t)) => t
      case Left(e) => failwith(e)
    }

    val interpEnv = ts.getInterpEnv
    val typeEnv = ts.getTypeEnv

    val newSort = Core.FiniteUniverseSort("_time_", 5)
    typeEnv |- newSort
    val concretizer = SortRenamer(Map(("time", newSort)))

    val newTs = TransformTransitionSystem(ts, concretizer)

    val tdlOutput = TDLPrinter(typeEnv, interpEnv)(newTs)
    println(s"OUTPUT: ===\n${tdlOutput}\n===")
  }
}
