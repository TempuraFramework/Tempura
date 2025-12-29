package tempura.smt

import tempura.expression.Core.*
import tempura.expression.Core.given
import tempura.helpers.Utils.*
import cats.implicits.*
import tempura.expression.Core
import tempura.expression.transforms.LetRemover

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

    private val sortMap: mutable.Map[Core.BoxedSort, String] = mutable.Map()
    private val exprMap: mutable.Map[Core.BoxedExpr, String] = mutable.Map()
    private val declarations: mutable.ListBuffer[String] = mutable.ListBuffer()
    private val assertions: mutable.ListBuffer[String] = mutable.ListBuffer()
    private val history: mutable.ListBuffer[String] = mutable.ListBuffer()

    private var stack: List[(Int, Int)] = Nil // (declCount, assertCount)
    private var currentModel: Option[SmtLibModel] = None

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
      sortMap.getOrElseUpdate(sort.box, sort match {
        case _: Core.BoolSort => "Bool"
        case _: Core.NumericSort => "Int"
        case Core.ArraySort(domain, range) => s"(Array ${lowerSort(domain)} ${lowerSort(range)})"
        case uninterpreted: Core.UnInterpretedSort => uninterpreted.sortName
        case alias: Core.AliasSort[?] => alias.sortName
        case finite: Core.FiniteUniverseSort => finite.sortName
        case datatype: Core.DatatypeConstructorSort => datatype.sortName
        case fun: Core.FunSort[?] =>
          unsupported(s"function sort lowering not supported in SMT-LIB printer: ${fun}")
      })

    override def lowerSort[A <: Core.Sort[A]](s: A): String = lowerSortName(s)

    override def defineSort[A <: Core.Sort[A]](s: A): String = {
      val lowered = s match {
        case _: Core.BoolSort => "Bool"
        case _: Core.NumericSort => "Int"
        case Core.ArraySort(domain, range) =>
          // Arrays don't need declaration, just lowering
          s"(Array ${lowerSort(domain)} ${lowerSort(range)})"
        case uninterpreted: Core.UnInterpretedSort =>
          // Generate declare-sort command
          val cmd = s"(declare-sort ${uninterpreted.sortName} ${uninterpreted.numArgs})"
          declarations.addOne(cmd)
          appendHistory(cmd)
          sortMap.update(s.box, uninterpreted.sortName)
          uninterpreted.sortName
        case alias @ Core.AliasSort(name, args, underlying) =>
          // Generate define-sort command
          // Use lowerSortName for underlying sort to avoid type issues
          val underlyingSortStr = lowerSortName(underlying)
          val argsStr = if args.isEmpty then "" else s" (${args.map(a => lowerSortName(a.sort)).mkString(" ")})"
          val cmd = s"(define-sort ${name}${argsStr} ${underlyingSortStr})"
          declarations.addOne(cmd)
          appendHistory(cmd)
          sortMap.update(s.box, name)
          name
        case finite: Core.FiniteUniverseSort =>
          // Generate datatype declaration for finite universe (as enum)
          val constructors = (0 until finite.card).map(i => s"(${getEnumName(i, finite)})").mkString(" ")
          val cmd = s"(declare-datatypes ((${finite.sortName} 0)) ((${constructors})))"
          declarations.addOne(cmd)
          appendHistory(cmd)
          sortMap.update(s.box, finite.sortName)
          finite.sortName
        case datatype: Core.DatatypeConstructorSort =>
          // Generate datatype declaration
          val constructorStrs = datatype.constructors.map { cons =>
            val argsStr = cons.args.map { case (name, argSort) =>
              s"(${name} ${lowerSort(argSort.sort)})"
            }.mkString(" ")
            if argsStr.isEmpty then
              s"(${cons.name})"
            else
              s"(${cons.name} ${argsStr})"
          }.mkString(" ")
          val cmd = s"(declare-datatypes ((${datatype.sortName} 0)) ((${constructorStrs})))"
          declarations.addOne(cmd)
          appendHistory(cmd)
          sortMap.update(s.box, datatype.sortName)
          datatype.sortName
        case fun: Core.FunSort[?] =>
          unsupported(s"function sort definition not supported in SMT-LIB printer: ${fun}")
      }
      lowered
    }

    override def declareVar[S <: Core.Sort[S]](name: String, sort: S): String = {
      val cmd = s"(declare-fun ${name} () ${lowerSort(sort)})"
      declarations.addOne(cmd)
      appendHistory(cmd)
      cmd
    }

    override def defineVar[S <: Core.Sort[S]](name: String, sort: S, expr: Core.Expr[S]): (String, List[String]) = {
      sort match {
        case funSort @ Core.FunSort(domainSorts, rangeSort) =>
          expr match {
            case Core.Macro(macroName, args, body) =>
              // Define function using define-fun
              val argsStr = args.map { case (argName, argSort) =>
                s"(${argName} ${lowerSort(argSort.sort)})"
              }.mkString(" ")
              val bodyStr = lower(body)
              val rangeSortStr = lowerSort(rangeSort)
              val cmd = s"(define-fun ${name} (${argsStr}) ${rangeSortStr} ${bodyStr})"
              declarations.addOne(cmd)
              appendHistory(cmd)
              (cmd, List())
            case Core.Var(_, _) =>
              // Uninterpreted function - just declare it
              val domSortsStr = domainSorts.map(s => lowerSort(s.sort)).mkString(" ")
              val rangeSortStr = lowerSort(rangeSort)
              val cmd = s"(declare-fun ${name} (${domSortsStr}) ${rangeSortStr})"
              declarations.addOne(cmd)
              appendHistory(cmd)
              (cmd, List())
            case _ =>
              // Other function expressions - use forall axiom
              val decl = declareVar(name, sort)
              val args = domainSorts.zipWithIndex.map { case (s, i) => (s"x${i}", s) }
              val forallAxiom = Core.mkForall(
                args,
                Core.mkEq(
                  Core.mkSubst("app", args.map(x => (x._1, Core.mkVar(x._1, x._2))), Core.mkVar(name, funSort)),
                  Core.mkSubst("app", args.map(x => (x._1, Core.mkVar(x._1, x._2))), expr)
                )
              )
              val axiomStr = s"(assert ${lower(forallAxiom)})"
              assertions.addOne(axiomStr)
              appendHistory(axiomStr)
              (decl, List(axiomStr))
          }
        case _ =>
          // Non-function variable
          val decl = declareVar(name, sort)
          val body = lower(expr)
          val eq = s"(assert (= ${name} ${body}))"
          assertions.addOne(eq)
          appendHistory(eq)
          (decl, List(eq))
      }
    }

    override def defineConst[S <: Core.Sort[S]](v: Core.SortValue[S]): String = lowerValue(v)

    override def lowerValue[S <: Core.Sort[S]](value: Core.SortValue[S]): String = value match {
      case Core.SortValue.BoolValue(b) => if b then "true" else "false"
      case Core.SortValue.NumericValue(n) => n.toString
      case Core.SortValue.UnInterpretedValue(name, _) => name
      case Core.SortValue.AliasSortValue(name, _) => name
      case Core.SortValue.FiniteUniverseValue(index, sort) =>
        getEnumName(index, sort)
      case Core.SortValue.DatatypeValue(constructorInst, _) =>
        val consName = constructorInst.constructor.name
        val args = constructorInst.params.map(param => lower(param.e))
        if args.isEmpty then
          consName
        else
          s"(${consName} ${args.mkString(" ")})"
      case Core.SortValue.ArrayValue(default, sort) =>
        // Constant array: ((as const (Array D R)) value)
        val domSort = lowerSort(sort.domainSort)
        val ranSort = lowerSort(sort.rangeSort)
        val defaultVal = lower(default)
        s"((as const (Array ${domSort} ${ranSort})) ${defaultVal})"
    }

    override def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): String = {
      val boxed = expr.box()
      exprMap.get(boxed) match {
        case Some(rendered) => rendered
        case None =>
          val lowered = lower(Map.empty)(expr)
          exprMap.update(boxed, lowered)
          lowered
      }
    }

    private def lower[S <: Core.Sort[S]](bound: Map[String, String])(expr: Core.Expr[S]): String = expr match {
      case Core.Var(name, _) => bound.getOrElse(name, name)
      case Core.Const(sortValue) =>
        sortValue match {
          case Core.SortValue.DatatypeValue(instantiatedCons, _) =>
            val consName = instantiatedCons.constructor.name
            val args = instantiatedCons.params.map(p => lower(bound)(p.e))
            if args.isEmpty then
              consName
            else
              s"(${consName} ${args.mkString(" ")})"
          case _ => lowerValue(sortValue)

        }
      // Binary operators
      case Core.Bop(op, lhs, rhs, _) => s"(${op} ${lower(bound)(lhs)} ${lower(bound)(rhs)})"

      // Unary operators
      case Core.Uop("as-array", lambdaExpr, _) =>
        // (as const (Array D R)) for constant arrays represented as lambdas
        unsupported("as-array lowering not fully supported in generic SMTLib Solver backend")
      case Core.Uop(op, sub, _) => s"(${op} ${lower(bound)(sub)})"
      // List operators (and, or, +, *, etc.)
      case Core.Lop(op, args, _, _) => s"(${op} ${args.map(lower(bound)).mkString(" ")})"

      // Ternary operator (ite)
      case Core.Top("ite", cond, thn, els, _) =>
        s"(ite ${lower(bound)(cond)} ${lower(bound)(thn)} ${lower(bound)(els)})"
      case Core.Top("=>", cond, thn, els, _) =>
        s"(=> ${lower(bound)(cond)} ${lower(bound)(thn)} ${lower(bound)(els)})"
      // Array operations
      case Core.ArraySelect(arr, idx) =>
        s"(select ${lower(bound)(arr)} ${lower(bound)(idx)})"
      case Core.ArrayStore(arr, idx, value) =>
        s"(store ${lower(bound)(arr)} ${lower(bound)(idx)} ${lower(bound)(value)})"

      // Quantifiers
      case Core.Forall(args, body) =>
        val binder = args.map { case (n, sort) => s"(${n} ${lowerSort(sort)})" }.mkString(" ")
        val extended = args.foldLeft(bound)((acc, entry) => acc.updated(entry._1, entry._1))
        s"(forall (${binder}) ${lower(extended)(body)})"
      case Core.Exists(args, body) =>
        val binder = args.map { case (n, sort) => s"(${n} ${lowerSort(sort)})" }.mkString(" ")
        val extended = args.foldLeft(bound)((acc, entry) => acc.updated(entry._1, entry._1))
        s"(exists (${binder}) ${lower(extended)(body)})"

      // Let expressions - expand them first
      case Core.Substitute("let", bindings, Core.Macro("letBody", _, _)) =>
        val letRemover = new LetRemover()
        val eliminated = letRemover.visit(Core.emptyInterpEnv)(expr)
        lower(bound)(eliminated)

      // Function application (Substitute with "app")
      case Core.Substitute("app", bindings, bodyExpr) =>
        bodyExpr match {
          case Core.Macro(name, args, _) =>
            // Application of a macro (defined function)
            val concreteArgs = bindings.map { case (_, arg) => lower(bound)(arg.e) }
            s"(${name} ${concreteArgs.mkString(" ")})"
          case Core.Var(name, _) =>
            // Application of an uninterpreted function
            val concreteArgs = bindings.map { case (_, arg) => lower(bound)(arg.e) }
            s"(${name} ${concreteArgs.mkString(" ")})"
          case other =>
            unsupported(s"cannot apply non-function expression in SMT-LIB printer: ${other}")
        }

      // Macros should not appear standalone
      case Core.Macro(name, _, _) =>
        unsupported(s"cannot treat a function symbol ${name} as an expression in SMT-LIB printer")

      case Core.DatatypeConstructorRecognizer(dt, consName, arg) =>
        s"(is-${consName} ${lower(bound)(arg)})"

      case other => unsupported(s"expression not supported by SMT-LIB printer: ${other}")
    }

    override def lookupDecl[S <: Sort[S]](v: String, s: S): Option[LoweredVarDecl] = {
      None // TODO
    }

    /**
     * Parse SMTLIB string representation of a sort back to Core.BoxedSort.
     * This provides basic support for common sorts.
     */
    override def liftSort(sortStr: String): Core.BoxedSort = {
      val trimmed = sortStr.trim
      trimmed match {
        case "Bool" => Core.BoolSort().box
        case "Int" => Core.NumericSort().box
        case s if s.startsWith("(Array ") && s.endsWith(")") =>
          // Parse (Array D R)
          val inner = s.substring(7, s.length - 1).trim
          val parts = splitSExpression(inner)
          if parts.length == 2 then
            val domSort = liftSort(parts(0))
            val ranSort = liftSort(parts(1))
            Core.arraySort(domSort, ranSort)
          else
            unsupported(s"liftSort: malformed array sort: ${sortStr}")
        case other =>
          // Check if it's in the type environment
          typeEnv.lookup(other).getOrElse {
            // Assume it's an uninterpreted sort
            Core.UnInterpretedSort(other, 0).box
          }
      }
    }

    /**
     * Parse SMTLIB string representation of a term back to Core.BoxedExpr.
     * This provides basic support for common expressions.
     */
    override def liftTerm(termStr: String): Core.BoxedExpr = {
      val trimmed = termStr.trim

      // Try to parse as a constant first
      trimmed match {
        case "true" => Core.mkTrue.box()
        case "false" => Core.mkFalse.box()
        case s if s.matches("-?\\d+") =>
          Core.mkConst(s.toInt).box()
        case s if s.startsWith("(") && s.endsWith(")") =>
          // Parse S-expression
          val inner = s.substring(1, s.length - 1).trim
          val parts = splitSExpression(inner)
          if parts.isEmpty then
            unsupported(s"liftTerm: empty S-expression")
          else {
            val op = parts.head
            val args = parts.tail

            op match {
              case "and" =>
                val liftedArgs = args.map(liftTerm)
                Core.unifyTerms(liftedArgs.toList, Core.BoolSort()) match {
                  case Some(unified) => Core.mkAnd(unified).box()
                  case None => unsupported(s"liftTerm: type mismatch in and: ${args.mkString(", ")}")
                }
              case "or" =>
                val liftedArgs = args.map(liftTerm)
                Core.unifyTerms(liftedArgs.toList, Core.BoolSort()) match {
                  case Some(unified) => Core.mkOr(unified).box()
                  case None => unsupported(s"liftTerm: type mismatch in or")
                }
              case "not" =>
                if args.length != 1 then unsupported(s"liftTerm: not expects 1 argument")
                val arg = liftTerm(args(0))
                arg.unify(Core.BoolSort()) match {
                  case Some(unified) => Core.mkNot(unified).box()
                  case None => unsupported(s"liftTerm: not argument is not boolean")
                }
              case "=>" =>
                if args.length != 2 then unsupported(s"liftTerm: => expects 2 arguments")
                val lhs = liftTerm(args(0))
                val rhs = liftTerm(args(1))
                (lhs.unify(Core.BoolSort()), rhs.unify(Core.BoolSort())).tupled match {
                  case Some((l, r)) => Core.mkImplies(l, r).box()
                  case None => unsupported(s"liftTerm: => arguments are not boolean")
                }
              case "=" =>
                if args.length != 2 then unsupported(s"liftTerm: = expects 2 arguments")
                val lhs = liftTerm(args(0))
                val rhs = liftTerm(args(1))
                rhs.e.unify(lhs.sort) match {
                  case Some(unified) => Core.mkEq(lhs.e, unified).box()
                  case None => unsupported(s"liftTerm: = type mismatch")
                }
              case "+" =>
                val liftedArgs = args.map(liftTerm)
                Core.unifyTerms(liftedArgs.toList, Core.NumericSort()) match {
                  case Some(unified) => Core.mkAdd(unified).box()
                  case None => unsupported(s"liftTerm: + type mismatch")
                }
              case "-" =>
                if args.length == 1 then
                  // Unary minus
                  val arg = liftTerm(args(0))
                  arg.unify(Core.NumericSort()) match {
                    case Some(unified) => Core.mkNegative(unified).box()
                    case None => unsupported(s"liftTerm: - argument is not numeric")
                  }
                else if args.length == 2 then
                  // Binary minus
                  val lhs = liftTerm(args(0))
                  val rhs = liftTerm(args(1))
                  (lhs.unify(Core.NumericSort()), rhs.unify(Core.NumericSort())).tupled match {
                    case Some((l, r)) => Core.mkMinus(l, r).box()
                    case None => unsupported(s"liftTerm: - type mismatch")
                  }
                else
                  unsupported(s"liftTerm: - expects 1 or 2 arguments")
              case "*" =>
                val liftedArgs = args.map(liftTerm)
                Core.unifyTerms(liftedArgs.toList, Core.NumericSort()) match {
                  case Some(unified) => Core.mkMul(unified).box()
                  case None => unsupported(s"liftTerm: * type mismatch")
                }
              case "<" | "<=" | ">" | ">=" =>
                if args.length != 2 then unsupported(s"liftTerm: ${op} expects 2 arguments")
                val lhs = liftTerm(args(0))
                val rhs = liftTerm(args(1))
                (lhs.unify(Core.NumericSort()), rhs.unify(Core.NumericSort())).tupled match {
                  case Some((l, r)) => Core.mkBop(op, l, r, Core.boolSort).box()
                  case None => unsupported(s"liftTerm: ${op} type mismatch")
                }
              case "ite" =>
                if args.length != 3 then unsupported(s"liftTerm: ite expects 3 arguments")
                val cond = liftTerm(args(0))
                val thn = liftTerm(args(1))
                val els = liftTerm(args(2))
                (cond.unify(Core.BoolSort()), thn.unify(els.sort)).tupled match {
                  case Some((c, t)) => Core.mkIte(c, t, els.e).box()
                  case None => unsupported(s"liftTerm: ite type mismatch")
                }
              case "select" =>
                if args.length != 2 then unsupported(s"liftTerm: select expects 2 arguments")
                val arr = liftTerm(args(0))
                val idx = liftTerm(args(1))
                arr.sort match {
                  case arrSort @ Core.ArraySort(_, _) =>
                    arr.unify(Core.ArraySort(idx.sort, arrSort.rangeSort)) match {
                      case Some(unified) => Core.mkSelect(unified, idx.e).box()
                      case None => unsupported(s"liftTerm: select index type mismatch")
                    }
                  case _ => unsupported(s"liftTerm: select on non-array")
                }
              case "store" =>
                if args.length != 3 then unsupported(s"liftTerm: store expects 3 arguments")
                val arr = liftTerm(args(0))
                val idx = liftTerm(args(1))
                val value = liftTerm(args(2))
                arr.unify(Core.ArraySort(idx.sort, value.sort)) match {
                  case Some(unified) => Core.mkStore(unified, idx.e, value.e).box()
                  case None => unsupported(s"liftTerm: store type mismatch")
                }
              case "forall" | "exists" =>
                if args.length != 2 then unsupported(s"liftTerm: ${op} expects 2 arguments")
                // Parse bound variables: ((x Sort) (y Sort) ...)
                val bindings = parseBindings(args(0))
                val body = liftTerm(args(1))
                body.unify(Core.BoolSort()) match {
                  case Some(unifiedBody) =>
                    if op == "forall" then
                      Core.mkForall(bindings, unifiedBody).box()
                    else
                      Core.mkExists(bindings, unifiedBody).box()
                  case None => unsupported(s"liftTerm: ${op} body is not boolean")
                }
              case _ =>
                // Could be a variable, uninterpreted function, or user-defined function
                interpEnv.lookup(op) match {
                  case Some(expr) =>
                    if args.isEmpty then
                      expr
                    else
                      // Function application - for now, just create a function application
                      // symbol since we don't have full type information
                      unsupported(s"liftTerm: function application not fully supported for ${op}")
                  case None =>
                    // Unknown identifier - create variable
                    if args.isEmpty then
                      Core.mkVar(op, Core.BoolSort()).box()
                    else
                      unsupported(s"liftTerm: unknown function: ${op}")
                }
            }
          }
        case varName =>
          // Variable name
          interpEnv.lookup(varName).getOrElse {
            Core.mkVar(varName, Core.BoolSort()).box()
          }
      }
    }

    override def liftFunc(func: String): Core.BoxedExpr =
      interpEnv.lookup(func).getOrElse(Core.mkVar(func, Core.BoolSort()).box())

    /**
     * Simple S-expression splitter. Splits top-level elements respecting parentheses.
     */
    private[smt] def splitSExpression(s: String): Array[String] = {
      val result = scala.collection.mutable.ArrayBuffer[String]()
      var depth = 0
      var current = new StringBuilder()
      var i = 0

      while i < s.length do {
        val c = s.charAt(i)
        c match {
          case '(' =>
            depth += 1
            current.append(c)
          case ')' =>
            depth -= 1
            current.append(c)
          case ' ' | '\t' | '\n' | '\r' if depth == 0 =>
            if current.nonEmpty then
              result += current.toString.trim
              current = new StringBuilder()
          case _ =>
            current.append(c)
        }
        i += 1
      }

      if current.nonEmpty then
        result += current.toString.trim

      result.toArray
    }

    /**
     * Parse quantifier bindings: ((x Int) (y Bool) ...) => List[(String, BoxedSort)]
     */
    private def parseBindings(bindingsStr: String): List[(String, Core.BoxedSort)] = {
      val trimmed = bindingsStr.trim
      if !trimmed.startsWith("(") || !trimmed.endsWith(")") then
        unsupported(s"parseBindings: malformed bindings: ${bindingsStr}")

      val inner = trimmed.substring(1, trimmed.length - 1).trim
      val bindings = splitSExpression(inner)

      bindings.map { binding =>
        val parts = splitSExpression(binding.substring(1, binding.length - 1))
        if parts.length != 2 then
          unsupported(s"parseBindings: malformed binding: ${binding}")
        val name = parts(0)
        val sort = liftSort(parts(1))
        (name, sort)
      }.toList
    }

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

    override def getModel: Option[SmtSolver.Model[String, String]] = currentModel

    override def getUnsatCore: Option[SmtSolver.UnsatCore[String, String]] = None // TODO

    override def checkSat(): SmtSolver.Result = SmtSolver.Result.UNKNOWN // TODO

    /**
     * Parse and store model output from an SMT solver.
     * The modelOutput should be the S-expression response to (get-model).
     * Example format:
     *   (model
     *     (define-fun x () Int 5)
     *     (define-fun y () Bool true)
     *   )
     */
    def setModelOutput(modelOutput: String): Unit = {
      try {
        currentModel = Some(SmtLibModel.parse(modelOutput, this))
      } catch {
        case e: Exception =>
          println(s"Warning: failed to parse model output: ${e.getMessage}")
          currentModel = None
      }
    }

    /** Render accumulated SMT-LIB commands. */
    def asScript: String =
      (declarations.toList ++ assertions.toList :+ "(check-sat)").mkString("\n")
  }

  /**
   * Model implementation for SmtLibSolver that parses SMTLIB model output.
   * Model format from (get-model) is typically:
   *   (model
   *     (define-fun var1 () Sort value1)
   *     (define-fun var2 ((x Sort1)) Sort2 body)
   *     ...
   *   )
   */
  class SmtLibModel(
    private val assignments: Map[String, (Core.BoxedSort, Core.BoxedExpr)],
    smtLibSolver: SmtLibSolver
  ) extends SmtSolver.Model[String, String](smtLibSolver) {

    override def formula(): Core.Expr[Core.BoolSort] = {
      val term = asTerm()
      solver.liftTerm(term).unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"SmtLibModel.formula(): model formula is not boolean")
      }
    }

    override def formula(vocab: Set[(String, Core.BoxedSort)]): Core.Expr[Core.BoolSort] = {
      val term = asTerm(vocab)
      solver.liftTerm(term).unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"SmtLibModel.formula(vocab): model formula is not boolean")
      }
    }

    override def valueOf[S <: Core.Sort[S]](name: String, sort: S): Option[Core.Expr[S]] = {
      assignments.get(name).flatMap { case (_, value) =>
        value.unify(sort)
      }
    }

    override def vocabulary(): (List[Core.BoxedSort], List[String]) = {
      val names = assignments.keys.toList
      val sorts = assignments.values.map(_._1).toList
      (sorts, names)
    }

    override def evaluate[S <: Core.Sort[S]](expr: Core.Expr[S]): Core.Expr[S] = {
      expr match {
        case Core.Var(name, sort) =>
          assignments.get(name) match {
            case Some((_, value)) =>
              value.unify(sort) match {
                case Some(unified) => unified
                case None => expr // Return original if type mismatch
              }
            case None => expr // Return original if not in model
          }
        case Core.Const(_) => expr
        case _ =>
          // For complex expressions, try to substitute variables
          // This is a simplified evaluation
          expr
      }
    }

    override def asNegatedTerm(): String = {
      val term = asTerm()
      s"(not ${term})"
    }

    override def asNegatedTerm(vocab: Set[(String, Core.BoxedSort)]): String = {
      val term = asTerm(vocab)
      s"(not ${term})"
    }

    override def asTerm(): String = {
      if assignments.isEmpty then
        "true"
      else {
        val equalities = assignments.map { case (name, (sort, value)) =>
          s"(= ${name} ${solver.lower(value.e)})"
        }.toList
        if equalities.length == 1 then
          equalities.head
        else
          s"(and ${equalities.mkString(" ")})"
      }
    }

    override def asTerm(vocabulary: Set[(String, Core.BoxedSort)]): String = {
      val relevantAssignments = vocabulary.flatMap { case (name, sort) =>
        assignments.get(name).map(value => (name, value))
      }
      if relevantAssignments.isEmpty then
        "true"
      else {
        val equalities = relevantAssignments.map { case (name, (sort, value)) =>
          s"(= ${name} ${solver.lower(value.e)})"
        }.toList
        if equalities.size == 1 then
          equalities.head
        else
          s"(and ${equalities.mkString(" ")})"
      }
    }

    override def apply(name: String, sort: Core.BoxedSort): Option[Core.BoxedExpr] = {
      assignments.get(name).map(_._2)
    }

    override def toString: String = {
      s"SmtLibModel { ${assignments.map { case (n, (s, v)) => s"$n = ${v.toString}" }.mkString(", ")} }"
    }
  }

  object SmtLibModel {
    /**
     * Parse SMTLIB model output into a SmtLibModel.
     * Expected format:
     *   (model
     *     (define-fun x () Int 5)
     *     (define-fun y () Bool true)
     *   )
     * Or just the list of definitions without the (model ...) wrapper.
     */
    def parse(modelOutput: String, solver: SmtLibSolver): SmtLibModel = {
      val trimmed = modelOutput.trim

      // Extract definitions from (model ...) wrapper if present
      val defsStr = if trimmed.startsWith("(model") then
        // Remove (model and closing )
        val inner = trimmed.substring(6, trimmed.lastIndexOf(')')).trim
        inner
      else
        trimmed

      // Split into individual definitions
      val definitions = extractDefinitions(defsStr)

      // Parse each definition
      val assignments = definitions.flatMap { defStr =>
        parseDefinition(defStr, solver)
      }.toMap

      new SmtLibModel(assignments, solver)
    }

    private def extractDefinitions(s: String): List[String] = {
      val result = scala.collection.mutable.ListBuffer[String]()
      var depth = 0
      var start = -1
      var i = 0

      while i < s.length do {
        val c = s.charAt(i)
        c match {
          case '(' =>
            if depth == 0 then start = i
            depth += 1
          case ')' =>
            depth -= 1
            if depth == 0 && start >= 0 then
              result += s.substring(start, i + 1)
              start = -1
          case _ =>
        }
        i += 1
      }

      result.toList
    }

    private def parseDefinition(defStr: String, solver: SmtLibSolver): Option[(String, (Core.BoxedSort, Core.BoxedExpr))] = {
      // Parse (define-fun name ((arg1 Sort1) ...) ReturnSort body)
      val trimmed = defStr.trim
      if !trimmed.startsWith("(define-fun") then
        return None

      try {
        // Remove (define-fun and closing )
        val inner = trimmed.substring(11, trimmed.lastIndexOf(')')).trim
        val parts = solver.splitSExpression(inner)

        if parts.length < 3 then
          return None

        val name = parts(0)
        val argsStr = parts(1) // Should be () for constants or ((x T) ...) for functions
        val sortStr = parts(2)
        val bodyStr = if parts.length > 3 then parts.drop(3).mkString(" ") else parts(2)

        // For now, only handle constants (nullary functions)
        if argsStr == "()" then
          val sort = solver.liftSort(sortStr)
          val value = solver.liftTerm(bodyStr)
          Some((name, (sort, value)))
        else
          // Skip functions with arguments for now
          None
      } catch {
        case e: Exception =>
          println(s"Warning: failed to parse definition: ${defStr}: ${e.getMessage}")
          None
      }
    }
  }
}
