package org.abstractpredicates.cozy

import org.abstractpredicates.parsing.io.{PathOf, StringReader}

import scala.reflect.ClassTag

object Cozy {

  enum Let[T](name: String, instance: T)(using val tag: ClassTag[T]) {
    case LetIn[X, Y](name: String, instance: X, next: Let[Y])(using xTag: ClassTag[X]) extends Let[X](name, instance)
    case In[X](name: String, instance: X)(using xTag: ClassTag[X]) extends Let[X](name, instance)(using xTag)
  }

  
  def allTransforms =
    List(
      PathOf,
      StringReader,
      
    )
}
