package org.abstractpredicates.helpers

import cats.data.Validated
import org.abstractpredicates.expression.Core
import shapeless3.typeable.Typeable

import scala.reflect.TypeTest
import shapeless3.typeable.syntax.typeable.cast

import scala.reflect.*
import scala.quoted.Type

object Utils {

  private var nameCnt: Int = 0

  def getUniqueName: String = {
    val s = "_unnamed_" + nameCnt
    nameCnt += 1
    s
  }

  def getUniqueName(suffix: String): String = {
    getUniqueName + "_" + suffix
  }

  extension [A, B](x: Either[A, B])
    def join(y: Either[A, B])(thenFun: (B, B) => Either[A, B], elseFun: (A, A) => Either[A, B]): Either[A, B] =
      (x, y) match {
        case (Right(xr), Right(yr)) => thenFun(xr, yr)
        case (Left(xl), Right(_)) => Left(xl)
        case (Right(_), Left(yr)) => Left(yr)
        case (Left(xe), Left(ye)) => elseFun(xe, ye)
      }

  extension [A, B](x: Either[(String, A), B])
    def updateError[Y](y: Y): Either[(String, Y), B] =
      x.fold((a, _) => Left(a, y), x => Right(x))
    def onSuccess[X](f: B => Either[(String, A), X]): Either[(String, A), X] =
      x match {
        case Right(r) => f(r)
        case Left(reason) => Left(reason)
      }

  extension [A, B](l: List[Either[A, B]])
    def joinAll(mergeFun: (A, A) => A): Either[A, List[B]] =
      l.foldLeft[Either[A, List[B]]](Right(List()))(
        (acc, curr) =>
          (curr, acc) match {
            case (Right(a), Right(l)) => Right(a :: l)
            case (Left(a), Right(_)) => Left(a)
            case (Right(_), Left(a)) => Left(a)
            case (Left(a), Left(b)) => Left(mergeFun(a, b))
          }
      )

  def failwith[A](msg: String): A = {
    throw new RuntimeException("failwith: " + msg)
  }

  def unsupported[A](msg: String): A = {
    throw new UnsupportedOperationException("unsupported: " + msg)
  }

  def unsupported[A, B](msg: String, obj: B): A = {
    throw new UnsupportedOperationException("unsupported: " + msg + " @ " + obj.toString)
  }


  def unexpected[A, B](msg: String, obj: B): A = {
    throw new RuntimeException("unexpected: " + msg + " @ " + obj.toString)
  }

  def unexpected[A](msg: String): A = {
    throw new RuntimeException("unexpected: " + msg)
  }

  def checked[A, B](s: Either[A, B]): Unit = {
    s match {
      case Right(_) => ()
      case Left(err) => failwith(s"checked: failed @ ${err.toString}")
    }
  }

  def returnChecked[A, B](s: Either[A, B]): B = {
    s match {
      case Right(b) => b
      case Left(err) => failwith(s"checked: failed @ ${err.toString}")
    }
  }


  // ML-style operators

  extension [A, B](a: A)
    infix def |>(f: A => B): B = f(a)

  extension [A, B](f: A => B)
    infix def @@(a: A): B = f(a)

  def ignore[A](x: A): Unit = ()

  // Canonical name for an alias of a parametric sort
  // This method gives the name of an AliasSort[T] instance
  def canonicalName(s0: Core.UnInterpretedSort, sArgs: List[Core.BoxedSort]): String = {
    s0.sortName + "__" + sArgs.map(x => x.sort.sortName).mkString("_")
  }

  // Canonical name for finite-universe sorts
  // XXX: Note naming starts at 1 and ends at n, inclusive!
  final def mkEnumNames(sortName: String, card: Int): List[String] = {
    (0 until card).map(n => "elt_" + n.toString + "_fd_" + sortName).toList
  }

  // Canonical name for a particular element in a finite-universe sort
  def getEnumName[S <: Core.Sort[S]](idx: Int, sort: S): String = {
    "elt_" + idx.toString + "_fd_" + sort.sortName
  }

  // Canonical name for a datatype recognizer
  def getRecognizerName(c: Core.Constructor): String = {
    "is_" + c.name
  }

  def getRecognizerName(c: String): String = {
    "is_" + c
  }

  def boundVarName(i: Int): String = s"__x_bnd_${i}"

  def testBoundVarName(s: String): Option[Int] =
    if (s.startsWith("__x_bnd_"))
      Some(s.substring(7).toInt)
    else
      None

  def id[A](x: A): A = x

  def flip[A, B, C](f: (A, B) => C): (B, A) => C = (b, a) => f(a, b)

  extension [A, B](p: (A, B))
    def fst: A = p._1
    def snd: B = p._2


  extension [A](lst: List[A])
    def mapi[B](f: (Int, A) => B): List[B] =
      lst.zipWithIndex.map { case (x, i) => f(i, x) }

  
  /** OS-specific helpers */
  enum OS {
    case Mac, Linux
    case Unknown(osString: String)
  }
  
  def getOS: OS = { 
    val osString = System.getProperty("os.name").toLowerCase
    if (osString.contains("mac") || osString.contains("darwin")) OS.Mac
    else if (osString.contains("linux")) OS.Linux
    else OS.Unknown(osString)
  }

  def getLinuxDesktop: Option[String] =
    if getOS != OS.Linux then None
    else {
      val env = System.getenv()
      val desktop = Option(env.get("XDG_CURRENT_DESKTOP"))
        .orElse(Option(env.get("DESKTOP_SESSION")))
        .map(_.toLowerCase)

      desktop.collect {
        case d if d.contains("kde") => "kde"
        case d if d.contains("gnome") => "gnome"
      }
    }

}
