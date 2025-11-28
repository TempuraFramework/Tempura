package org.abstractpredicates.parsing.io

import org.abstractpredicates.helpers.TempuraTransform
import org.abstractpredicates.expression.Core 
import org.abstractpredicates.parsing.sexpr.ParseTree 

class SexprReader extends TempuraTransform[String, List[ParseTree]] {
  override def apply(te: Core.TypeEnv, ie: Core.InterpEnv)(e: String) : Either[String, List[ParseTree]] = {
    ???
  }
}
