package tempura.cozy

import scala.annotation.{MacroAnnotation, experimental}
import scala.quoted.Quotes
import scala.reflect.runtime.universe.ModuleDef

@experimental
case class AutoRegister(name: String) extends MacroAnnotation {
  
  override def transform(using quotes: Quotes)(
    definition: quotes.reflect.Definition,
    companion: Option[quotes.reflect.Definition]
  ): List[quotes.reflect.Definition] = {
    import quotes.reflect.*

    definition match {
      // A 'val' or 'var' instance
      case v: ValDef =>
        List(definition)
      // objects
      case m: ModuleDef =>
        List(definition)
      // A class, trait, or object
      case c: ClassDef =>
        // Check for 'Module' flag to identify an 'object'
        if c.symbol.flags.is(Flags.Module) then
          List(definition)
        else
          report.error("This annotation is only allowed on 'object' or 'val' instances.", c.pos)
          List(definition)

      case _ =>
        report.error("Unsupported target for this annotation, objects or instances only", definition.pos)
        List(definition)
    }
  }
}