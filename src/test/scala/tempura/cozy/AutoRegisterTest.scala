package tempura.cozy

import scala.annotation.experimental

@experimental
object AutoRegisterTest {

  trait X

  trait Y

  trait Z

  @AutoRegister("hello")
  object X {}

  @AutoRegister("hello2")
  object Y {}

  def foo(): Z = {
    @AutoRegister("hello3")
    val z = new Z {}
    z
  }

  // this will fail
  //@AutoRegister("hello-fail")
  //case class ZImp() extends Z 
}

