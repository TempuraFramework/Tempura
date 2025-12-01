package org.abstractpredicates.parsing.io

import org.abstractpredicates.helpers.Transforms.{BasicTransform, pipeline}
import org.abstractpredicates.parsing.sexpr.{ParseTree, StringToSExprParser}

import java.nio.file.{Files, Path}

object SexprReader extends BasicTransform[String, List[ParseTree]] {

  override def apply(a: String): Either[String, List[ParseTree]] = {
    pipeline[String](List(PathOf.box, StringReader.box, StringToSExprParser.box))(a) match {
      case Right(t) => Right(t.asInstanceOf[List[ParseTree]])
      case Left(r) => Left(r)
    }
  }


}