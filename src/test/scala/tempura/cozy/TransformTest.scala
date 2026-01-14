package tempura.cozy

import org.scalatest.funsuite.AnyFunSuite
import tempura.cozy.Transforms.{Transform, compose}

import java.nio.file.Path

class TransformTest extends AnyFunSuite {


  // ---------------------------------------------------------------------------
  // Example passes (3 stages)
  // ---------------------------------------------------------------------------
  object Pass1_PathOf extends Transform[Tuple1[String], Tuple1[Path]]:
    def apply(in: Tuple1[String]): Either[String, Tuple1[Path]] =
      Right(Tuple1(Path.of(in._1)))

  object Pass2_RequireScala extends Transform[Tuple1[Path], Tuple1[Path]]:
    def apply(in: Tuple1[Path]): Either[String, Tuple1[Path]] =
      val p = in._1
      if p.toString.endsWith(".scala") then Right(Tuple1(p))
      else Left(s"Not a .scala file: $p")

  object Pass3_NameAndLen extends Transform[Tuple1[Path], (String, Int)]:
    def apply(in: Tuple1[Path]) =
      val name = in._1.getFileName.toString
      Right((name, name.length))

  // TODO: more this somewhere else.
  test("testCompose") {
    // You can build the pipeline either way:
    val pipeline1 = Pass1_PathOf *: Pass2_RequireScala *: Pass3_NameAndLen *: EmptyTuple
    val pipeline2 = (Pass1_PathOf, Pass2_RequireScala) // also works

    val ok = compose(Tuple1("src/Main.scala"), pipeline1)
    val bad = compose(Tuple1("README.md"), pipeline1)

    println(ok)
    println(bad)
  }


}
