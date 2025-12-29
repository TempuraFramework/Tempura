package tempura.abstraction

trait GaloisConnection[C, A](using C: AbstractDomain[C], A: AbstractDomain[A]) {

  // The alpha operator
  def abstraction(c: C): A

  // The gamma operator
  def concretization(a: A): C

  // Best transformer: α ∘ f ∘ γ where f is concrete transformer
  def bestTransformer(abstractValue: A, concreteTransformer: C => C): A = {
    abstraction(concreteTransformer(concretization(abstractValue)))
  }
}
