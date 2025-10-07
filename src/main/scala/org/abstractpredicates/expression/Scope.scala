package org.abstractpredicates.expression

class Scope(initialTypeEnv: Core.TypeEnv, initialInterpEnv: Core.InterpEnv) {

  private var typeEnv: Core.TypeEnv = initialTypeEnv
  private var interpEnv: Core.InterpEnv = initialInterpEnv

  def addSort[T <: Core.Sort[T]](name: String, sort: T): Unit = {
    typeEnv = typeEnv.add(name, sort)
  }

  def addVar[T <: Core.Sort[T]](name: String, e: Core.Expr[T]): Unit = {
    interpEnv = interpEnv.add(name, e)
  }

  def getTypeEnv: Core.TypeEnv = typeEnv

  def getInterpEnv: Core.InterpEnv = interpEnv

}
