package tempura.cozy

import clojure.lang.{Symbol, *}
import tempura.expression.Core
import tempura.helpers.Utils.unexpected
import tempura.smt.SmtSolver.SolverEnvironment
import tempura.cozy.CExpr
import tempura.parsing.sexpr.{ParseTree, SmtlibParser, StringToSExprParser, TDLParser}
import tempura.expression.Syntax.*

import scala.collection.mutable.{ListBuffer, HashMap as HM}
import scala.annotation.static
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import clojure.lang.RT.{CURRENT_NS, `var` as rt_var}
import cats.implicits.*
import tempura.cozy.Transforms.compose
import tempura.parsing.io.{PathOf, StringReader, TDLReader}
import tempura.smt.{Cvc5Solver, Z3Solver}
import tempura.smt.SmtInterpolSolver.SmtInterpolSolver

import scala.collection.immutable.VectorBuilder

// companion trait;
// needed by @static annotation
sealed trait CS

// CS stands for "CozyScript" --- main entry for Clojure interop
object CS {

  //////
  // book-keeping for shadow-state of Clojure interpreter
  // default namespace of Clojure is "user"
  private final val ENV: HM[String, CozyNamespace] = new mutable.HashMap()
  private final val EVAL = rt_var("clojure.core", "eval")
  private final val DEFAULT_NS = Namespace.findOrCreate(Symbol.intern("user"))

  ENV.update("user", new CozyNamespace(DEFAULT_NS, Core.emptyTypeEnv, Core.emptyInterpEnv))

  // XXX: must be after the previous statement
  private [cozy] var currentNS = ENV("user")

  // retrieves name of current namespace
  @static private def getCurrentNsName: String = currentNS.getNamespace.getName.getName

  // help
  @static def cozyHelp: AnyRef = {
      "Cozy: Available commands under (C ...)\n" +
      "  (C (sort <name>)) - create uninterpreted sort\n" +
      "  (C (finite-sort <name> <size>)) - create finite sort\n" +
      "  (C (create-solver <solver name> <solver type>\n" +
      "TODO"
  }


  // partially evaluates Cozy expressions, optionally sending sub-expressions to Clojure runtime
  @static def cozyEval(e: CExpr): AnyRef = {
    import CExpr.*
    val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
    e match {
      case CSeq(Vector(CSymbol("sort", _), CSymbol(sortName, sortNamespace))) =>
        val output = new ListBuffer[String]()
        if getCurrentNsName != sortNamespace then {
          output.addOne(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${sortNamespace}, not current namespace ${getCurrentNsName}.")
        }
        ENV.get(sortNamespace) match {
          case Some(ns) =>
            typeEnv |- Core.UnInterpretedSort(sortName, 0)
            output.addOne(s"Cozy: Creating uninterpreted sort $sortName in namespace $sortNamespace")
        }
        println(output.toList.mkString("\n"))
        RT.`var`(getCurrentNsName, sortName, typeEnv(sortName).get)
      case CSeq(Vector(CSymbol("finite-sort", _), CSymbol(sortName, sortNamespace), CInt(sz))) =>
        val output = new ListBuffer[String]()
        if getCurrentNsName != sortNamespace then {
          output.addOne(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${sortNamespace}, not current namespace ${getCurrentNsName}.")
        }
        ENV.get(sortNamespace) match {
          case Some(ns) =>
            typeEnv |- Core.FiniteUniverseSort(sortName, sz.toInt)
            output.addOne(s"Cozy: Creating finite sort $sortName of size ${sz.toInt}")
        }
        output.toList.mkString("\n")
        println(output)
        RT.`var`(getCurrentNsName, sortName, typeEnv(sortName).get)
      case CSeq(Vector(CSymbol("var", _), CSymbol(varName, varNamespace), sortExpr)) =>
        val output = new ListBuffer[String]()
        if getCurrentNsName != varNamespace then {
          output.addOne(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${varNamespace}, not current namespace ${getCurrentNsName}.")
        }

        ENV.get(varNamespace) match {
          case Some(ns) =>
            CozyToExpr.cozyParseSort(sortExpr) match {
              case Right(s) =>
                interpEnv |- (varName, s)
                output.addOne(s"Cozy: Creating variable $varName of sort $s in namespace $varNamespace")
              case Left(err) =>
                output.addOne(s"Cozy: error encountered creating variable ${err}")
            }
          case None =>
            output.addOne(s"Cozy: Error: ${varNamespace} not found.")
        }
        println(output.toList.mkString("\n"))
        RT.`var`(varName, getCurrentNsName, interpEnv(varName))
      case CSeq(Vector(CSymbol("create-solver", _), CSymbol(solverName, solverNs), CKeyword(solverNickName, _))) =>
        val output = new ListBuffer[String]()
        val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
        solverName match {
          case "z3" =>
            val slv = Z3Solver.Z3Solver(typeEnv, interpEnv)
            currentNS.addSolverEnv(solverNickName, slv.box)
            output.addOne(s"Cozy: Solver ${solverNickName} for z3 added to current namespace")
          case "cvc5" =>
            val slv = Cvc5Solver.Cvc5Solver(typeEnv, interpEnv)
            currentNS.addSolverEnv(solverNickName, slv.box)
            output.addOne(s"Cozy: Solver ${solverNickName} for cvc5 added to current namespace")
          case "smtinterpol" =>
            val slv = SmtInterpolSolver(typeEnv, interpEnv)
            currentNS.addSolverEnv(solverNickName, slv.box)
            output.addOne(s"Cozy: Solver ${solverNickName} for smtinterpol added to current namespace")
          case _ =>
            output.addOne("Cozy: Solver can only be one of {z3, cvc5, smtinterpol} right now.")
        }
        println(output.toList.mkString("\n"))
        RT.`var`(getCurrentNsName, solverNickName, currentNS.solvers(solverNickName))
      case CSeq(Vector(CSymbol("read-tdl", _), CSymbol(varName, _), CString(path))) =>
        val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
        val pipeline = PathOf *: StringReader *: StringToSExprParser *: EmptyTuple
        val result: Either[String, Tuple1[List[ParseTree]]] = compose(Tuple1(path), pipeline)
        result match {
          case Right(Tuple1(parsed)) =>
            TDLParser((typeEnv, interpEnv, parsed)) match {
              case Right(Tuple1(parsedTs)) =>
                RT.`var`(getCurrentNsName, varName, parsedTs)
              case Left(e) => e.asInstanceOf[AnyRef]
            }
          case e =>
            (s"err: TDLReader: Expected List of ParseTree objects but got ${e}").asInstanceOf[AnyRef]
        }
      case _ =>
        CString(s"Cozy: I'm sorry. I don't understand your command ${e.toString}. Maybe try (C help)?")
    }
    CInt(0)
  }

  // get the parent namespace, which provides the (typeEnv, interpEnv, ?solvers) for the current namespace (if any)
  // returns a pair (CozyNamespace, Boolean) where the second parameter tells us whether
  // to clone the solvers map
  private def getParentNs(cargs: IPersistentList): Option[(CozyNamespace, Boolean)] = {
    import CExpr.*
    val converted = ilist2vec(cargs)
    var arg: Option[(CozyNamespace, Boolean)] = None
    converted foreach {
      case CSeq(Vector(CKeyword("inherit", _), CSymbol(name, _), _)) =>
        arg = Some(ENV(name), false)
      case CSeq(Vector(CKeyword("inherit-all", _), CSymbol(name, _), _)) =>
        arg = Some(ENV(name), true)
      case _ => ()
    }
    arg
  }

  // get name of a namespace from a namespace creation command in Clojure
  private def getNsName(l: IPersistentList): (String, IPersistentStack) = {
    val nsArgs = l.pop()
    val nsname = nsArgs.peek().asInstanceOf[String]
    (nsname, nsArgs)
  }

  // perform creation of shadow-state variables in Cozy for corresponding Clojure
  // (create-ns ...), (ns ...) commands
  private def evalCreateNs(l: IPersistentList): (AnyRef, CozyNamespace) = {
    val (nsname, nsArgs) = getNsName(l)
    val result = EVAL.invoke(l)
    getParentNs(l) match {
      case Some(parent, false) => // inherit typeEnv, interpEnv from parent only
        val cns = new CozyNamespace(Namespace.find(Symbol.intern(nsname)), parent.getTypeEnv.copy(), parent.getInterpEnv.copy())
        ENV.update(nsname, cns)
        (result, cns)
      case Some(parent, true) => // inherit typeEnv, interpEnv + solvers from parent
        val cns = CozyNamespace(Namespace.find(Symbol.intern(nsname)), parent.getTypeEnv.copy(), parent.getInterpEnv.copy(), parent.getSolverEnvs.clone())
        ENV.update(nsname, cns)
        (result, cns)
      case None => // do not inherit from parent, roll our own shadow-state variables
        val cns = new CozyNamespace(Namespace.find(Symbol.intern(nsname)), Core.emptyTypeEnv, Core.emptyInterpEnv)
        ENV.update(nsname, cns)
        (result, cns)
    }
  }

  // proxies commands sent to the Clojure repl
  @static def eval(arg: AnyRef): AnyRef = {
    println(s"CS.eval: received ${arg.getClass.getName} (${arg})\n")

    arg match {
      case l: IPersistentList =>
        try {
          val c = l.peek()
          c match {
            case s: Symbol =>
              s.getName match {
                case "C" =>
                  val cArgs = l.pop()
                  println("C [ " + cArgs + " ]")
                  val argsT = convert(cArgs)
                  cozyEval(convert(cArgs))
                case "create-ns" =>
                  val r = evalCreateNs(l)
                  r._1
                case "ns" =>
                  val r = evalCreateNs(l)
                  currentNS = r._2
                  r._1
                case "in-ns" =>
                  currentNS = ENV(getNsName(l)._1)
                  EVAL.invoke(l)
                case _ => EVAL.invoke(arg)
              }
            case _ =>
              EVAL.invoke(arg)
          }
        } catch {
          case _: Throwable =>
            EVAL.invoke(arg)
        }
      case _ =>
        EVAL.invoke(arg)
    }
  }

  // inspects Cozy AST and returns result to Clojure repl
  @static def inspect(e: CExpr): String = e.toString

  // converts a Clojure expression. covers the fragment of clojure we support.
  @static def convert(x: AnyRef): CExpr = {
    import CExpr.*
    x match {
      case null => CNil()
      case s: Symbol => CSymbol(s.getName, s.getNamespace)
      case k: Keyword => CKeyword(k.getName, namespace = k.getNamespace)
      case seq: ISeq => /* lists are ISeqs */ CSeq(iseq2vec(seq))
      case v: IPersistentVector => /* e.g. [1 2 3] */ CVec(ivec2arr(v))
      case m: IPersistentMap => /* e.g. {"Fred" 100, "Bob" 120, "Stella", 130} */ CMap(imap2map(m))
      case s: IPersistentSet => /* e.g. #{"Alice", "Bob", "Wortel"} */ CSet(iset2set(s))
      case l: Long => CInt(l)
      case s: String => CString(s)
      case b: Boolean => CBool(b)
      case other => CObject(other)
    }
  }

  // ... and back
  @static def revert(ex: CExpr): AnyRef = {
    import CExpr.*
    ex match {
      case CNil() => null
      case CSymbol(name, ns) => Symbol.intern(ns, name)
      case CKeyword(name, ns) => Keyword.intern(ns, name)
      case CSeq(args) => vec2iseq(args)
      case CObject(obj) => obj
      case CMap(m) => map2imap(m)
      case CSet(s) => set2iset(s)
      case CVec(v) => arr2ivec(v)
      case CInt(i) => i.asInstanceOf[AnyRef]
      case CString(s) => s.asInstanceOf[AnyRef]
      case CBool(b) => b.asInstanceOf[AnyRef]
    }
  }

  // converts a Clojure list to a scala Vector
  @static def ilist2vec(l: IPersistentList): Vector[CExpr] = {
    iseq2vec(l.seq())
  }

  // converts a Clojure sequence to a scala Vector
  @static def iseq2vec(seq: ISeq): Vector[CExpr] =
    Iterator.iterate(seq)(_.next).takeWhile(_ != null)
      .map(_.first)
      .map(convert)
      .toVector

  // ... and back
  @static def vec2iseq(vec: Vector[CExpr]): ISeq =
    RT.seq(vec.map(revert).asJava)

  // converts a Clojure vector into a scala Array
  @static def ivec2arr(vec: IPersistentVector): Array[CExpr] = {
    val len = vec.length()
    val arr = new Array[CExpr](len)
    (0 until len) foreach {
      idx =>
        arr(idx) = convert(vec.valAt(idx))
    }
    arr
  }

  // ... and back
  @static def arr2ivec(arr: Array[CExpr]): IPersistentVector =
    RT.vector(arr.map(revert) *)

  // converts a Clojure map into a Scala map
  @static def imap2map(m: IPersistentMap): Map[CExpr, CExpr] = {
    m.iterator().asScala.map {
      case e: IMapEntry => (convert(e.key()), convert(e.`val`())) // IMapEntry extends java.util.Map.Entry :contentReference[oaicite:6]{index=6}
      case e: java.util.Map.Entry[?, ?] => (convert(e.getKey), convert(e.getValue))
      case other =>
        unexpected(s"Unexpected element from IPersistentMap iterator: ${other.getClass}: $other")
    }.toMap
  }

  // ... and back
  @static def map2imap(m: Map[CExpr, CExpr]): IPersistentMap = {
    val arr: Array[AnyRef] = new Array[AnyRef](m.size * 2)
    var idx = 0
    m foreach {
      (key, v) =>
        arr(idx) = revert(key)
        idx += 1
        arr(idx) = revert(v)
        idx += 1
    }
    RT.map(arr *)
  }

  // converts a Clojure set into a Scala set
  @static def iset2set(is: IPersistentSet): Set[CExpr] = {
    iseq2vec(is.seq()).map(x => convert(x)).toSet
  }

  // ... and back
  @static def set2iset(s: Set[CExpr]): IPersistentSet = {
    val arr: Array[AnyRef] = new Array(s.size)
    var idx = 0
    s foreach {
      elt =>
        arr(idx) = elt
        idx += 1
    }
    RT.set(arr *)
  }
}
