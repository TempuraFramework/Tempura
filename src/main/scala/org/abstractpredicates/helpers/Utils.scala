package org.abstractpredicates.helpers

import cats.data.Validated
import org.abstractpredicates.expression.Core
import shapeless3.typeable.Typeable

import scala.reflect.TypeTest
import shapeless3.typeable.syntax.typeable.cast

import scala.collection.mutable.ListBuffer
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

  // Cached desktop environment detection result
  private var cachedDesktop: Option[Option[String]] = None

  /**
   * Detect Linux desktop environment using multiple strategies:
   * 1. Environment variables (fastest, most reliable when present)
   * 2. PDF mime handler (direct signal for PDF viewer preference)
   * 3. Running processes (slowest, least reliable, last resort)
   *
   * Returns normalized DE name: "kde", "gnome", "xfce", etc.
   * Returns None if detection fails or not on Linux.
   */
  def getLinuxDesktop: Option[String] = {
    if getOS != OS.Linux then None
    else {
      cachedDesktop match {
        case Some(result) => result
        case None =>
          val result = detectDesktopEnvVars()
            .orElse {
              println("trying strategy 2")
              detectDesktopFromPdfMime()
            }.orElse {
              println("trying strategy 3")
              detectDesktopFromProcesses()
            }
          cachedDesktop = Some(result)
          result
      }
    }
  }

  /** Strategy 1: Check standard desktop environment variables */
  private def detectDesktopEnvVars(): Option[String] = {
    try {
      val env = System.getenv()

      // Try multiple env vars in order of reliability
      Option(env.get("XDG_CURRENT_DESKTOP"))
        .orElse(Option(env.get("XDG_SESSION_DESKTOP")))
        .orElse(Option(env.get("DESKTOP_SESSION")))
        .orElse(Option(env.get("GDMSESSION")))
        .orElse(Option(env.get("KDE_FULL_SESSION")).filter(_ == "true").map(_ => "KDE"))
        .orElse(Option(env.get("GNOME_DESKTOP_SESSION_ID")).map(_ => "GNOME"))
        .map(_.toLowerCase)
        .flatMap(normalizeDesktopName)
    } catch {
      case _: Exception => None
    }
  }

  /** Strategy 2: Infer desktop from configured PDF viewer (task-specific heuristic) */
  private def detectDesktopFromPdfMime(): Option[String] = {
    import scala.sys.process._
    try {
      // Query default PDF handler via xdg-mime or gio
      val pdfHandler =
        scala.util.Try(Seq("xdg-mime", "query", "default", "application/pdf").!!.trim.toLowerCase)
          .orElse(scala.util.Try(Seq("gio", "mime", "application/pdf").!!.trim.toLowerCase))
          .toOption
      println(s"pdfHandler: ${pdfHandler}")
      pdfHandler.flatMap {
        case h if h.contains("okular") => Some("kde")
        case h if h.contains("evince") || h.contains("eog") => Some("gnome")
        case h if h.contains("atril") => Some("mate")
        case h if h.contains("qpdfview") => Some("kde")
        case h if h.contains("libreoffice") => Some("kde")
        case _ => None
      }
    } catch {
      case _: Exception => None
    }
  }

  /** Strategy 3: Check for desktop-specific running processes (last resort) */
  private def detectDesktopFromProcesses(): Option[String] = {
    import scala.sys.process._
    try {
      val processes = Seq("ps", "-eo", "comm").!!.toLowerCase

      // Check for specific desktop process signatures
      if processes.contains("plasmashell") ||
        processes.contains("kwin_x11") ||
        processes.contains("kwin_wayland") then Some("kde")
      else if processes.contains("gnome-shell") then Some("gnome")
      else if processes.contains("xfce4-session") then Some("xfce")
      else if processes.contains("mate-session") then Some("mate")
      else None
    } catch {
      case _: Exception => None
    }
  }

  /** Normalize desktop name to canonical form */
  private def normalizeDesktopName(name: String): Option[String] = {
    name.toLowerCase match {
      case d if d.contains("kde") || d.contains("plasma") => Some("kde")
      case d if d.contains("gnome") => Some("gnome")
      case d if d.contains("xfce") => Some("xfce")
      case d if d.contains("mate") => Some("mate")
      case d if d.contains("lxde") => Some("lxde")
      case d if d.contains("lxqt") => Some("lxqt")
      case d if d.contains("cinnamon") => Some("cinnamon")
      case d if d.nonEmpty => Some(d)
      case _ => None
    }
  }

  trait AccumulatingEntry[T] {
    def add(t: T*): Unit

    def addNamed(ts: (T, String)*): Unit

    def get: List[(String, T)]

    def getContent: List[T]

    def reset(): Unit

    def length: Int

    def isEmpty: Boolean

    def getName: String
  }

  object AccumulatingEntry {
    def apply[T](name: String): AccumulatingEntry[T] =
      new AccumulatingEntry[T] {
        private var cnt = 0
        private var buffer: scala.collection.mutable.Map[String, T] = scala.collection.mutable.Map[String, T]()

        override def add(t: T*): Unit =
          t foreach { x =>
            buffer.update(getName + "_" + cnt.toString, x)
            cnt += 1
          }

        override def addNamed(ts: (T, String)*): Unit =
          ts foreach { x =>
            buffer.update(x._2, x._1)
          }

        override def get: List[(String, T)] = this.buffer.toList

        override def getContent: List[T] = this.buffer.values.toList

        override def reset(): Unit = {
          this.buffer = scala.collection.mutable.Map()
        }

        override def length: Int = this.buffer.size

        override def isEmpty: Boolean = this.buffer.isEmpty

        override def toString: String = getName + " {" + buffer.toString + "}"

        override def getName: String = name
      }
  }

  def cartesianProduct[A](domains: List[List[A]]): List[List[A]] =
    domains match
      case Nil => List(List.empty[A])
      case head :: tail =>
        for
          element <- head
          combination <- cartesianProduct(tail)
        yield element :: combination

  // Exact runtime casting
  def exactCast[T](x: Any)(using ct: ClassTag[T]): Option[T] =
    if x != null && x.getClass == ct.runtimeClass then
      Some(x.asInstanceOf[T])
    else
      None

  // Exact casting of ClassTags
  def exactTagCast[X, T](ct: ClassTag[X])(using ctY: ClassTag[T]): Option[ClassTag[T]] =
    if ct.runtimeClass == ctY.runtimeClass then
      // the asInstanceOf is “morally safe” because of the runtime check
      Some(ct.asInstanceOf[ClassTag[T]])
    else
      None
}
