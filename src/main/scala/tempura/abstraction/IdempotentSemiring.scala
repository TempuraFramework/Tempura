package tempura.abstraction

import algebra.Eq
import algebra.ring.Semiring as S


trait IdempotentSemiring[T] extends S[T], AbstractDomain[T] {
  
  override def isZero(a: T)(implicit ev: Eq[T]): Boolean = super.isZero(a)

  override def join(lhs: T, rhs: T): T = plus(lhs, rhs)
  
  override def meet(lhs: T, rhs: T) : T = times(lhs, rhs)
}
