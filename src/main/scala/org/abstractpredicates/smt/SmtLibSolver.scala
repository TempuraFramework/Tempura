package org.abstractpredicates.smt

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Core.given
import org.abstractpredicates.helpers.Utils.*

import scala.collection.mutable

/**
 * Lightweight SMT-LIB printer backend. It lowers Core expressions to concrete SMT-LIB commands
 * but does not execute a concrete solver. The backend is useful for debugging and for exporting
 * verification problems. All solver operations update an internal buffer that can be rendered via
 * [[asScript]]. `checkSat` always returns [[SmtSolver.Result.UNKNOWN]].
 */
object SmtLibSolver {

  def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv): SmtLibSolver =
    new SmtLibSolver(typeEnv, interpEnv)

  final class SmtLibSolver(private val typeEnv: Core.TypeEnv, private val interpEnv: Core.InterpEnv)
    extends SmtSolver.Solver[String, String](typeEnv, interpEnv) {

    override type LoweredSort = String

    private val sortCache: mutable.Map[Core.BoxedSort, String] = mutable.Map()
    private val exprCache: mutable.Map[Core.BoxedExpr, String] = mutable.Map()
    private val declarations: mutable.ListBuffer[String] = mutable.ListBuffer()
    private val assertions: mutable.ListBuffer[String] = mutable.ListBuffer()
    private val history: mutable.ListBuffer[String] = mutable.ListBuffer()

    private var stack: List[(Int, Int)] = Nil // (declCount, assertCount)

    private def appendHistory(entry: String): Unit =
      history.prepend(entry)

    override def getHistory: List[String] = history.toList

    typeEnv.registerUpdateHook((name, sort) => {
      val lowered = defineSort(sort.sort)
      s"; define-sort ${name}: ${lowered}"
    })

    interpEnv.registerUpdateHook((name, boxedExpr) => {
      val sort = boxedExpr.sort
      val decl = declareVar(name, sort)
      val (_, axioms) = defineVar(name, sort, boxedExpr.e)
      axioms.foreach(assertions.addOne)
      decl
    })

    private def lowerSortName[A <: Core.Sort[A]](sort: A): String =
      sortCache.getOrElseUpdate(sort.box, sort match {
        case _: Core.BoolSort => "Bool"
        case _: Core.NumericSort => "Int"
        case Core.ArraySort(domain, range) => s"(Array ${lowerSort(domain)} ${lowerSort(range)})"
        case uninterpreted: Core.UnInterpretedSort => uninterpreted.sortName
        case alias: Core.AliasSort[?] =>
          unsupported(s"alias sort lowering not supported in SMT-LIB printer: ${alias}")
        case finite: Core.FiniteUniverseSort => finite.sortName
        case fun: Core.FunSort[?] =>
          unsupported(s"function sort lowering not supported in SMT-LIB printer: ${fun}")
        case datatype: Core.DatatypeConstructorSort =>
          unsupported(s"datatype sort lowering not supported in SMT-LIB printer: ${datatype}")
      })

    override def lowerSort[A <: Core.Sort[A]](s: A): String = lowerSortName(s)

    override def defineSort[A <: Core.Sort[A]](s: A): String = lowerSortName(s)

    override def declareVar[S <: Core.Sort[S]](name: String, sort: S): String = {
      val cmd = s"(declare-fun ${name} () ${lowerSort(sort)})"
      declarations.addOne(cmd)
      appendHistory(cmd)
      cmd
    }

    override def defineVar[S <: Core.Sort[S]](name: String, sort: S, expr: Core.Expr[S]): (String, List[String]) = {
      val decl = declareVar(name, sort)
      val body = lower(expr)
      val eq = s"(assert (= ${name} ${body}))"
      assertions.addOne(eq)
      appendHistory(eq)
      (decl, List(eq))
    }

    override def defineConst[S <: Core.Sort[S]](v: Core.SortValue[S]): String = lowerValue(v)

    override def lowerValue[S <: Core.Sort[S]](value: Core.SortValue[S]): String = value match {
      case Core.SortValue.BoolValue(b) => if b then "true" else "false"
      case Core.SortValue.NumericValue(n) => n.toString
      case Core.SortValue.UnInterpretedValue(name, _) => name
      case other => unsupported(s"literal not supported by SMT-LIB printer: ${other}")
    }

    override def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): String = {
      val boxed = expr.box()
      exprCache.get(boxed) match {
        case Some(rendered) => rendered
        case None =>
          val lowered = lower(Map.empty)(expr)
          exprCache.update(boxed, lowered)
          lowered
      }
    }

    private def lower[S <: Core.Sort[S]](bound: Map[String, String])(expr: Core.Expr[S]): String = expr match {
      case Core.Var(name, _) => bound.getOrElse(name, name)
      case Core.Const(sortValue) => lowerValue(sortValue)
      case Core.Bop(op, lhs, rhs, _) => s"(${op} ${lower(bound)(lhs)} ${lower(bound)(rhs)})"
      case Core.Uop(op, sub, _) => s"(${op} ${lower(bound)(sub)})"
      case Core.Lop(op, args, _, _) => s"(${op} ${args.map(lower(bound)).mkString(" ")})"
      case Core.Top("ite", cond, thn, els, _) =>
        s"(ite ${lower(bound)(cond)} ${lower(bound)(thn)} ${lower(bound)(els)})"
      case Core.ArraySelect(arr, idx) =>
        s"(select ${lower(bound)(arr)} ${lower(bound)(idx)})"
      case Core.ArrayStore(arr, idx, value) =>
        s"(store ${lower(bound)(arr)} ${lower(bound)(idx)} ${lower(bound)(value)})"
      case Core.Forall(args, body) =>
        val binder = args.map { case (n, sort) => s"(${n} ${lowerSort(sort)})" }.mkString(" ")
        val extended = args.foldLeft(bound)((acc, entry) => acc.updated(entry._1, entry._1))
        s"(forall (${binder}) ${lower(extended)(body)})"
      case Core.Exists(args, body) =>
        val binder = args.map { case (n, sort) => s"(${n} ${lowerSort(sort)})" }.mkString(" ")
        val extended = args.foldLeft(bound)((acc, entry) => acc.updated(entry._1, entry._1))
        s"(exists (${binder}) ${lower(extended)(body)})"
      case other => unsupported(s"expression not supported by SMT-LIB printer: ${other}")
    }

    override def lookupDecl[S <: Sort[S]](v: String, s: S): Option[LoweredVarDecl] = {
      None // TODO
    }

    override def liftTerm(expr: String): Core.BoxedExpr =
      unsupported("liftTerm is not supported for SMT-LIB printer backend")

    override def liftSort(sort: String): Core.BoxedSort =
      unsupported("liftSort is not supported for SMT-LIB printer backend")

    override def liftFunc(func: String): Core.BoxedExpr =
      interpEnv.lookup(func).getOrElse(Core.mkVar(func, Core.BoolSort()).box())

    override def initialize(logicOptions: SmtSolver.Logic): Unit = {
      appendHistory(s"; set-logic ${SmtSolver.parseLogic(logicOptions)}")
    }
    
    override def add(fs: List[Core.BoxedExpr]): List[String] = {
      val lowered = fs.map(expr => s"(assert ${lower(expr.e)})")
      lowered.foreach(assertions.addOne)
      lowered.foreach(appendHistory)
      lowered
    }

    override def addTerms(terms: List[String]): List[String] = {
      terms.foreach(assertions.addOne)
      terms.foreach(appendHistory)
      terms
    }

    override def push(): Unit = {
      stack = (declarations.size, assertions.size) :: stack
      appendHistory("; push")
    }

    override def pop(): Unit = stack match {
      case (declCount, assertCount) :: rest =>
        while declarations.size > declCount do declarations.remove(declarations.size - 1)
        while assertions.size > assertCount do assertions.remove(assertions.size - 1)
        stack = rest
        appendHistory("; pop")
      case Nil => ()
    }

    override def reset(): Unit = {
      declarations.clear()
      assertions.clear()
      stack = Nil
      appendHistory("; reset")
    }

    override def fork(): SmtLibSolver =
      val clone = new SmtLibSolver(typeEnv.copy(), interpEnv.copy())
      clone.declarations ++= this.declarations
      clone.assertions ++= this.assertions
      clone.history ++= this.history
      clone.stack = this.stack
      clone

    override def getModel: Option[SmtSolver.Model[String, String]] = None // TODO 

    override def getUnsatCore: Option[SmtSolver.UnsatCore[String, String]] = None // TODO

    override def checkSat(): SmtSolver.Result = SmtSolver.Result.UNKNOWN // TODO 

    /** Render accumulated SMT-LIB commands. */
    def asScript: String =
      (declarations.toList ++ assertions.toList :+ "(check-sat)").mkString("\n")
  }
}
