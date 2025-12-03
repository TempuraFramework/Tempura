package org.abstractpredicates.helpers

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtSolver.SolverEnvironment

import scala.annotation.tailrec
import scala.reflect.ClassTag

object Transforms {
  trait TempuraTransform {
    def getName: String
  }

  sealed trait BoxedTempuraTransform {
    def getName: String
  }

  trait BasicTransform[A, B](using val aTag: ClassTag[A], val bTag: ClassTag[B]) extends TempuraTransform {
    // ensure all subclasses are objects
    self: Singleton =>

    override def getName: String = self.getClass.getName

    def apply(a: A): Either[String, B]
  }

  trait EnvTransform[A, B](using val aTag: ClassTag[A], val bTag: ClassTag[B]) extends TempuraTransform {
    // ensure all subclasses are objects
    self: Singleton =>

    def getName: String = self.getClass.getName

    def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(a: A): Either[String, B]

  }

  trait SolverAidedTransform[A, B](using val aTag: ClassTag[A], val bTag: ClassTag[B]) extends TempuraTransform {
    // ensure all subclasses are objects
    self: Singleton =>

    def getName: String = self.getClass.getName

    def apply(solver: SolverEnvironment)(a: A): Either[String, B]

  }

  trait WithTransform[T, A, B](val tTag: ClassTag[T], val aTag: ClassTag[A], val bTag: ClassTag[B]) extends TempuraTransform {
    self: Singleton =>
    
    def getName: String = self.getClass.getName
    
    def apply[TT](t: TT)(a: A): Either[String, B]
  }
  
  trait BoxedBasicTransform extends BoxedTempuraTransform {
    type A
    type B
    val transform: BasicTransform[A, B]

    override def getName: String = transform.getName
  }

  trait BoxedEnvTransform extends BoxedTempuraTransform {
    type A
    type B
    val transform: EnvTransform[A, B]
    
    override def getName: String = transform.getName
  }

  trait BoxedSolverAidedTransform extends BoxedTempuraTransform {
    type A
    type B
    val transform: SolverAidedTransform[A, B]
    
    override def getName: String = transform.getName
  }

  trait BoxedaWithTransform extends BoxedTempuraTransform {
    type T
    type A
    type B
    val transform: WithTransform[T, A, B]
    override def getName: String = transform.getName
  }
  
  extension [S, T](trans: BasicTransform[S, T]) {
    def box: BoxedBasicTransform {type A = S; type B = T} =
      new BoxedBasicTransform {
        override type A = S
        override type B = T
        override val transform: BasicTransform[S, T] = trans
      }

  }
  
  extension [S, T](trans: EnvTransform[S, T]) {
    def box: BoxedEnvTransform {type A = S; type B = T} =
      new BoxedEnvTransform {
        override type A = S
        override type B = T
        override val transform: EnvTransform[S, T] = trans
      }

  }

  extension [S, T](trans: SolverAidedTransform[S, T]) {
    def box: BoxedSolverAidedTransform {type A = S; type B = T} =
      new BoxedSolverAidedTransform {
        override type A = S
        override type B = T
        override val transform: SolverAidedTransform[S, T] = trans
      }
  }

  extension [W, X, Y](trans: WithTransform[W, X, Y]) {
    def box: BoxedaWithTransform {type T = W; type A = X;type B = Y} =
      new BoxedaWithTransform {
        override type T = W
        override type A = X
        override type B = Y
        override val transform: WithTransform[T, A, B] = trans
      }
  }
  
  /**
   * TODO: There's as bit of a code smell here, where class tags are associated with the uncontainerized / unboxed
   * trait instead of the containerized trait. This causes a fair bit of code duplication when we code up the 
   * pipeline method --- it can only be defined per implementation of the containerized trait instead of at the trait
   * level. Admittedly the signatures for each transform class is a bit different, which is itself another design
   * issue that currently doesn't have a good solution yet (maybe HLists?). 
   */


  def pipeline[A](bs: List[BoxedBasicTransform])(initVal: A): Either[String, Any] = {
    bs match {
      case first :: next :: rest =>
        initVal match {
          case first.transform.aTag(aVal) =>
            first.transform(aVal) flatMap {
              case next.transform.aTag(x) => pipeline(next :: rest)(x)
              case _ => Left(s"error: couldn't typecheck transform's return type ${first.transform.bTag.toString} against expected type ${next.transform.aTag.toString}")
            }
          case _ => Left(s"error: couldn't typecheck value ${initVal} of type ${initVal.getClass.getName} against ${first.transform.aTag.toString}")
        }
      case List(last) =>
        initVal match {
          case last.transform.aTag(aVal) =>
            last.transform(aVal)
          case _ =>
            Left(s"error: couldn't typecheck value ${initVal} of type ${initVal.getClass.getName} against ${last.transform.aTag.toString}")
        }
      case List() =>
        Right(initVal)
    }
  }


  def pipeline[A](bs: List[BoxedEnvTransform])(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(initVal: A): Either[String, Any] = {
    bs match {
      case first :: next :: rest =>
        initVal match {
          case first.transform.aTag(aVal) =>
            first.transform(typeEnv, interpEnv)(aVal) flatMap {
              case next.transform.aTag(x) => pipeline(next :: rest)(typeEnv, interpEnv)(x)
              case _ => Left(s"error: couldn't typecheck transform's return type ${first.transform.bTag.toString} against expected type ${next.transform.aTag.toString}")
            }
          case _ => Left(s"error: couldn't typecheck value ${initVal} of type ${initVal.getClass.getName} against ${first.transform.aTag.toString}")
        }
      case List(last) =>
        initVal match {
          case last.transform.aTag(aVal) =>
            last.transform(typeEnv, interpEnv)(aVal)
        }
      case List() =>
        Right(initVal)
    }
  }

  def pipeline[A](bs: List[BoxedSolverAidedTransform])(solverEnv: SolverEnvironment)(initVal: A): Either[String, Any] = {
    bs match {
      case first :: next :: rest =>
        initVal match {
          case first.transform.aTag(aVal) =>
            first.transform(solverEnv)(aVal) flatMap {
              case next.transform.aTag(x) => pipeline(next :: rest)(solverEnv)(x)
              case _ => Left(s"error: couldn't typecheck transform's return type ${first.transform.bTag.toString} against expected type ${next.transform.aTag.toString}")
            }
          case _ => Left(s"error: couldn't typecheck value ${initVal} of type ${initVal.getClass.getName} against ${first.transform.aTag.toString}")
        }
      case List(last) =>
        initVal match {
          case last.transform.aTag(aVal) =>
            last.transform(solverEnv)(aVal)
        }
      case List() =>
        Right(initVal)
    }
  }

  
}