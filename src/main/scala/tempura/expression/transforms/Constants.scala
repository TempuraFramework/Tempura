package tempura.expression.transforms

import tempura.expression.Core.InterpEnv
import tempura.expression.Core
import scala.collection.mutable

object Constants {

  class ConstantVisitor extends Visitor {
    private val constants : mutable.Set[Core.BoxedSortValue] = mutable.Set()
    
    override def constVisitor[A <: Core.Sort[A]](env: InterpEnv)(v: Core.Const[A]): Core.Expr[A] = {
      constants.add(v.sortValue.box)
      super.constVisitor(env)(v)
    }
    
    def getConstants : Set[Core.BoxedSortValue] = constants.toSet
  }
  
  def apply[S <: Core.Sort[S]](interpEnv: InterpEnv)(expr: Core.Expr[S]): Set[Core.BoxedSortValue] =
    val visitor = new ConstantVisitor()
    visitor.visit(interpEnv)(expr)
    visitor.getConstants
}
