package tempura.abstraction

trait StarSemiring[T] extends IdempotentSemiring[T] {
  def star(t: T) : T 
}
