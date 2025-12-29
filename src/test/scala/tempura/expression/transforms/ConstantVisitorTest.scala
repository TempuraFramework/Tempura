package tempura.expression.transforms

import org.scalatest.funsuite.AnyFunSuite
import tempura.expression.Syntax.*
import tempura.expression.Core

class ConstantVisitorTest extends AnyFunSuite {

  test("const-visitor-test-1") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val tyT = typeEnv |- Core.UnInterpretedSort("T", 0)
    val x = interpEnv |- ("x", tyT)

    val arr = interpEnv |- ("arr", Core.ArraySort(tyT, tyT))
    val arrStore = Core.mkConstArray(tyT, x)

    val expr = Core.mkEq(arr, arrStore) /\ 
      Core.mkEq(Core.mkConst(Core.SortValue.NumericValue(3)), Core.mkConst(Core.SortValue.NumericValue(4))) \/ Core.mkFalse \/ Core.mkFalse \/ Core.mkTrue


    val v = Constants(interpEnv)(expr)

    assert(v == Set(Core.SortValue.NumericValue(3).box,
      Core.SortValue.NumericValue(4).box,
      Core.SortValue.BoolValue(true).box,
      Core.SortValue.BoolValue(false).box,
      Core.SortValue.ArrayValue(x, Core.ArraySort(tyT, tyT)).box
    ))

    println(s"v: ${v}")

  }

}
