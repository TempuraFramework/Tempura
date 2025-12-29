package tempura.abstraction

import tempura.expression.Core
import tempura.transitions.TransitionSystem

case class TransitionSystemProjection(ts: TransitionSystem, fsTs: TransitionSystem,
                                      sortMap: Map[Core.BoxedSort, Core.BoxedSort]) {
  
  def originalSystem: TransitionSystem = ts 
  
  def transformedSystem: TransitionSystem = fsTs

}

// TODO TODO FIXME
/*
given projScheme: ProjectionScheme[TransitionSystem] with {

  override def apply: Map[String, Core.BoxedSort] = ???
}

given projectable: Projectable[TransitionSystem] with {
  override def projectionScheme: ProjectionScheme[TransitionSystem] = ???

  override def project(scheme: ProjectionScheme[TransitionSystem], item: TransitionSystem): TransitionSystem = ???
}*/