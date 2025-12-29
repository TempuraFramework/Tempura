package tempura.cozy

import tempura.expression.Core
import tempura.smt.SmtSolver.SolverEnvironment
import tempura.helpers.Utils

import scala.annotation.tailrec
import scala.deriving.Mirror
import scala.compiletime.{constValueTuple, erasedValue, summonInline}
import scala.reflect.ClassTag
import cats.implicits.*

import java.nio.file.Path

object Transforms {

  // utilities for transforming a list of Any objects into a tuple
  object ReifyToTuple {
    inline def toTuple[T <: Tuple](xs: Seq[Any]): Either[String, T] =
      decodeRec[T](xs.toList, 0)

    private inline def decodeRec[T <: Tuple](xs: List[Any], i: Int): Either[String, T] =
      inline erasedValue[T] match
        case _: EmptyTuple =>
          xs match
            case Nil => Right(EmptyTuple.asInstanceOf[T])
            case _ => Left(s"Too many args: expected $i, got ${i + xs.length}")

        case _: (h *: t) =>
          xs match
            case Nil => Left(s"Missing arg #${i + 1}")
            case x :: rest =>
              for
                head <- cast[h](x, i)
                tail <- decodeRec[t](rest, i + 1)
              yield (head *: tail).asInstanceOf[T]

    private inline def cast[H](x: Any, i: Int): Either[String, H] =
      inline erasedValue[H] match
        case _: Int =>
          x match
            case j: java.lang.Integer => Right(j.intValue.asInstanceOf[H])
            case _ => Left(s"arg#${i + 1}: expected Int, got ${x.getClass.getName}")

        case _: Boolean =>
          x match
            case b: java.lang.Boolean => Right(b.booleanValue.asInstanceOf[H])
            case _ => Left(s"arg#${i + 1}: expected Boolean, got ${x.getClass.getName}")

        case _ =>
          // For reference types, do an erased runtime check via ClassTag.
          val ct = summonInline[ClassTag[H]] // summoning delayed until after inlining :contentReference[oaicite:2]{index=2}
          if ct.runtimeClass.isInstance(x) then Right(x.asInstanceOf[H])
          else Left(s"arg#${i + 1}: expected ${ct.runtimeClass.getName}, got ${x.getClass.getName}")
  }

  // all callable transforms from
  trait Transform[In <: Tuple, Out <: Tuple] { self => 
    // self: Singleton => // XXX: don't restrict to singletons now, instead we use annotations to 
    // mark out what instances can be added to the set of Cozy primitives
    def apply(in: In): Either[String, Out]
  }

  // for calling from Clojure
  object TransformInterop {

    trait DynTransform {
      def apply(args: List[Any]): Either[String, Any]
    }

    // callTransform(tr, args) calls a transform with an untyped argument list.
    inline def callTransform[In <: Tuple, Out <: Tuple](
                                                         tr: Transform[In, Out],
                                                         args: List[Any]
                                                       ): Either[String, Out] =
      ReifyToTuple.toTuple[In](args).flatMap(tr.apply)

  }

  /////////////////////////////////
  // type-safe composition of transforms

  // RF: I multi-shot prompted this code.
  // in below code, everything is a tuple
  // Compose[In, Ts] feeds an input of type In into a pipeline of type Ts

  trait Compose[In <: Tuple, Ts <: Tuple]:
    type Out <: Tuple

    def run(in: In, ts: Ts): Either[String, Out]

  // companion object to the above trait.

  object Compose:
    type Aux[In <: Tuple, Ts <: Tuple, Out0 <: Tuple] = Compose[In, Ts] {type Out = Out0}

    // Extract the output tuple type of the head transform H, given the current input In
    type MidOf[In <: Tuple, H] <: Tuple = H match
      case Transform[`In`, mid] => mid

    given base[In <: Tuple]: Aux[In, EmptyTuple, In] =
      new Compose[In, EmptyTuple]:
        type Out = In

        def run(in: In, ts: EmptyTuple): Either[String, Out] = Right(in)

    // Key change: do NOT ask the compiler to infer Mid.
    // Instead compute Mid = MidOf[In, H] by matching on H's type.
    given step[In <: Tuple, H, Tail <: Tuple](using
                                              headEv: H <:< Transform[In, MidOf[In, H]],
                                              tailC: Compose[MidOf[In, H], Tail]
                                             ): Aux[In, H *: Tail, tailC.Out] =
    new Compose[In, H *: Tail]:
      type Out = tailC.Out

      def run(in: In, ts: H *: Tail): Either[String, Out] =
        val head: Transform[In, MidOf[In, H]] = headEv(ts.head)
        head.apply(in).flatMap(mid => tailC.run(mid, ts.tail))

  // Entry point
  def compose[In <: Tuple, Ts <: Tuple](input: In, transforms: Ts)(using c: Compose[In, Ts])
  : Either[String, c.Out] =
    c.run(input, transforms)

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
  def testCompose(): Unit =
    // You can build the pipeline either way:
    val pipeline1 = Pass1_PathOf *: Pass2_RequireScala *: Pass3_NameAndLen *: EmptyTuple
    val pipeline2 = (Pass1_PathOf, Pass2_RequireScala) // also works

    val ok = compose(Tuple1("src/Main.scala"), pipeline1)
    val bad = compose(Tuple1("README.md"), pipeline1)

    println(ok)
    println(bad)
}