package tempura.cozy

import tempura.expression.Core
import tempura.smt.SmtSolver.SolverEnvironment
import tempura.helpers.Utils

import scala.annotation.tailrec
import scala.deriving.Mirror
import scala.compiletime.{constValueTuple, erasedValue, summonInline}
import scala.reflect.ClassTag
import cats.implicits.*
import tempura.helpers.Utils.ReifyToTuple

import java.nio.file.Path

object Transforms {


  // all callable transforms from
  trait Transform[In <: Tuple, Out <: Tuple] {
    self =>
    // self: Singleton => // XXX: don't restrict to singletons now, instead we use annotations to 
    // mark out what instances can be added to the set of Cozy primitives
    def apply(in: In): Either[String, Out]

    def applyUntyped(args: List[Any]): AnyRef = {
      Utils.ReifyToTuple.toTuple(args) flatMap { typedArgs => apply(typedArgs) } match {
        case Right(out) => Utils.ReifyToTuple.fromTuple(out).asInstanceOf[AnyRef]
        case Left(errMsg) => Utils.failwith("Transform.applyunTyped: " + errMsg)
      }
    }
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

}