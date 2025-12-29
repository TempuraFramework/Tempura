package tempura.abstraction

trait Projectable[A] {
  def projectionScheme: ProjectionScheme[A]
  def project(scheme: ProjectionScheme[A], item: A) : A
}
