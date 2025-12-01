package org.abstractpredicates.helpers

import org.abstractpredicates.helpers.Transforms.*
import org.abstractpredicates.parsing.io.{PathOf, StringReader, TDLReader, VMTReader}
import org.abstractpredicates.parsing.printers.{FormulaPrinter, TDLPrinter, VMTPrinter}
import org.abstractpredicates.parsing.sexpr.{SmtlibParser, StringToSExprParser, TDLParser, VMTParser}

import scala.annotation.StaticAnnotation
import scala.collection.mutable

object TransformRegistry {

  private val transformRegistry: mutable.Map[String, BoxedTempuraTransform] = mutable.Map.empty

  private[helpers] def register(name: String, transform: BoxedTempuraTransform): Unit = {
    println(s"putting ${name}, ${transform}")
    transformRegistry.put(name, transform)
  }

  List(
    PathOf.box,
    StringReader.box,
    TDLReader.box,
    VMTReader.box,
    FormulaPrinter.box,
    TDLPrinter.box,
    VMTPrinter.box,
    SmtlibParser.box,
    StringToSExprParser.box,
    TDLParser.box,
    VMTParser.box
  ).foreach(x =>

    register(x.getName.strip().split("\\.").toList.reverse.head.stripSuffix("$"), x))

  def getRegistry: Map[String, BoxedTempuraTransform] =
    transformRegistry.toMap

  def apply(name: String): Option[BoxedTempuraTransform] =
    transformRegistry.get(name)

  override def toString: String = {
    this.transformRegistry.toList.map(x =>
      x._1 + " : " + (x._2 match {
        case b: BoxedBasicTransform =>
          b.transform.getName
        case e: BoxedEnvTransform =>
          e.transform.getName
        case s: BoxedSolverAidedTransform =>
          s.transform.getName
      })
    ).mkString("; ")
  }
}