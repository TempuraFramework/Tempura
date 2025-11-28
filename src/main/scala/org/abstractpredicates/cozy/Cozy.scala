package org.abstractpredicates.cozy

import scala.reflect.ClassTag

object Cozy {

  trait Transform[A, B, C](using val aTag: ClassTag[A], val bTag: ClassTag[B], val cTag: ClassTag[C]) {
    def apply(a: A): Either[B, C]

    def getATag: ClassTag[A] = aTag
    def getBTag: ClassTag[B] = bTag
    def getCTag: ClassTag[C] = cTag
  }
  /*
  object Transform {
    def apply[A, B, C](f: A => Either[B, C])(using aTag: ClassTag[A], bTag: ClassTag[B]): Transform[A, B, C] = new Transform[A, B, C] {
      override def apply(a: A): Either[B, C] = f(a)
    }
  }
  */
  /*
  enum TransformTree[A, B, C](name: String)(using val aTag: ClassTag[A], val bTag: ClassTag[B], val cTag: ClassTag[C]) {
    case Internal[X, Y, Z, R1, R2](name: String, 
                           f: Transform[X, Y, Z],
                           thenTransform: TransformTree[Y, Y1, Y2],
                                          elseTransform: TransformTree[Z, Z1, Z2]) 
      extends TransformTree[X, Y, Z](name)(using f.getATag, f.getBTag, thenTransform.getBTag, thenTransform.getCTag, elseTransform.getBTag, elseTransform.getCTag)
    case Leaf(name: String, f: Transform[A, B, C]) extends TransformTree[A, B, C](name)(using f.getATag, f.getBTag, f.getCTag)

    def getATag: ClassTag[A] = aTag
    def getBTag: ClassTag[B] = bTag
    def getCTag: ClassTag[C] = cTag
    
    def apply(a: A): Either[B, C] =
      this match {
        case Internal(name, f, next) =>
          f(a).flatMap(next(_))
        case EndStage(_, f) => f(a)
      }
  }

  enum Let[T](name: String, instance: T)(using val tag: ClassTag[T]) {
    case LetIn[X, Y](name: String, instance: X, next: Let[Y])(using xTag: ClassTag[X]) extends Let[X](name, instance)
    case In[X](name: String, instance: X)(using xTag: ClassTag[X]) extends Let[X](name, instance)(using xTag)
  }*/
  
  

}
