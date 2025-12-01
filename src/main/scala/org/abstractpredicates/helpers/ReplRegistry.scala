package org.abstractpredicates.helpers

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.BoxedExpr
import org.abstractpredicates.smt.SmtSolver.SolverEnvironment

import scala.collection.mutable
import scala.collection.mutable.Map as MMap

object ReplRegistry {
  
  trait Value { type T; val value: T}
  object Value { 
    def make[V](v: V): Value {type T = V} = new Value { override type T = V; override val value = v }
  } 
  
  type PipelineStage =  ReplRegistry.Value => Either[String, ReplRegistry.Value]
  
  def wrap[A](e: Either[String, A]) : Either[String, Value] =
    e match {
      case Right(a) => Right(Value.make(a))
      case Left(err) => Left(err)
    }
  
  def runPipeline(p: Value => Either[String, Value])(input: Value) : Either[String, Value] = p(input)

  def runPipeline(s: String)(input: Value): Either[String, Value] = 
    getPipeline(s) match {
      case Some(p) => p(input)
      case None => Left(s"pipeline ${s} not found")
    }

  // TODO: make this changeable in the future
  final def getProjectionSize: Int = 6
  
  
  private val valuesRegistry : MMap[String, Value] = mutable.Map()
  private val typeEnvRegistry: MMap[String, Core.TypeEnv] = mutable.Map()
  private val interpEnvRegistry: MMap[String, Core.InterpEnv] = mutable.Map()
  private val pipelineRegistry: MMap[String, Value => Either[String, Value]] = mutable.Map()
  private val solverRegistry: MMap[String, SolverEnvironment] = mutable.Map()

  def addValue(name: String, v: Value): Unit = valuesRegistry.update(name, v)
  def getValue(name: String) : Option[Value] = valuesRegistry.get(name)
  def addTypeEnv(name: String, v: Core.TypeEnv): Unit = typeEnvRegistry.update(name, v)
  def getTypeEnv(name: String) : Option[Core.TypeEnv] = typeEnvRegistry.get(name)
  def addInterpEnv(name: String, v: Core.InterpEnv): Unit = interpEnvRegistry.update(name, v)
  def getInterpEnv(name: String) : Option[Core.InterpEnv] = interpEnvRegistry.get(name)
  def addPipeline(name: String, p: Value => Either[String, Value]): Unit = pipelineRegistry.update(name, p)
  def getPipeline(name: String): Option[Value => Either[String, Value]] = pipelineRegistry.get(name)
}
