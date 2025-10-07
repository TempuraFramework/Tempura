package org.abstractpredicates.expression

import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Core
import org.abstractpredicates.helpers.Utils.*

class UnInterpretedSortConcretizer(renamedSorts: Map[String, BoxedSort]) extends ExprTransformer {
  
  override def varTransformer[A <: Core.Sort[A]](env: InterpEnv)(v: Var[A]): Core.BoxedExpr = {
    (v.sort, renamedSorts.get(v.sort.sortName)) match {
      case (_, Some(newSort: BoxedSort)) => 
        Var(v.name, newSort)
      case _ => v
    }
  }

  // TODO: how to handle uninterpreted constants? ---> Need to impose some sort of ordering over universe elements.
  override def constTransformer[A <: Core.Sort[A]](env: InterpEnv)(v: Const[A]): Core.BoxedExpr = {
    v.sortValue match {
      case u: Core.SortValue.UnInterpretedValue =>
        renamedSorts.get(u.sort.sortName) match {
          case Some(_) => failwith("cannot handle uninterpreted constants")
          case _ => v 
        }
      case _ => v
    }
  }
  
  
}
