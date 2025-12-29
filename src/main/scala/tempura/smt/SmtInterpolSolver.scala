package tempura.smt

import de.uni_freiburg.informatik.ultimate.logic.{FunctionSymbol, Logics, Script, SMTLIBConstants, Sort, Term, TermVariable}
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol
import tempura.expression.Core.*
import tempura.helpers.Utils.*

import scala.collection.mutable
import cats.implicits.*
import tempura.expression.Core
import tempura.expression.transforms.LetRemover
import scala.jdk.CollectionConverters.*

object SmtInterpolSolver {

  /** Log levels for SMTInterpol solver output */
  enum LogLevel(val value: Int) {
    case OFF extends LogLevel(0) // No logging
    case FATAL extends LogLevel(1) // Only fatal errors
    case ERROR extends LogLevel(2) // Errors and fatal (recommended default)
    case WARN extends LogLevel(3) // Warnings and above
    case INFO extends LogLevel(4) // Info and above (verbose)
    case DEBUG extends LogLevel(5) // Debug and above (very verbose)
    case TRACE extends LogLevel(6) // Everything (extremely verbose)
  }


  class SmtInterpolSolver(
                           private val typeEnv: Core.TypeEnv,
                           private val interpEnv: Core.InterpEnv,
                           private val logLevel: LogLevel = LogLevel.ERROR
                         ) extends SmtSolver.Solver[Term, FunctionSymbol](typeEnv, interpEnv) {

    override type LoweredSort = Sort

    private val logger = new DefaultLogger
    logger.setLoglevel(logLevel.value)
    private val solver = new SMTInterpol(logger)

    private val funMap: mutable.Map[String, FunctionSymbol] = mutable.Map()
    private val sortMap: mutable.Map[Core.BoxedSort, Sort] = mutable.Map()
    private val exprMap: mutable.Map[Core.BoxedExpr, Term] = mutable.Map()
    private val axiomsMap: mutable.Map[String, Term] = mutable.Map()
    private var history: List[String] = Nil
    private var logic: SmtSolver.Logic = SmtSolver.arithFree
    private var activeLogic: Option[String] = None

    def getSolver: SMTInterpol = solver

    /** Get the current log level of this solver */
    def getLogLevel: LogLevel = logLevel

    private def record(entry: String): Unit = history = entry :: history

    override def getHistory: List[String] = history

    private def mkDatatypeSort(sort: Core.DatatypeConstructorSort): Sort = {
      val datatype = solver.datatype(sort.sortName, 0)
      val constructors = sort.constructors.map { constructor =>
        val selectorNames = constructor.args.map(_._1).toArray
        val selectorSorts = constructor.args.map { case (_, argSort) =>
          if argSort.sort == sort then solver.sort(sort.sortName)
          else lowerSort(argSort.sort)
        }.toArray
        solver.constructor(constructor.name, selectorNames, selectorSorts)
      }.toArray
      solver.declareDatatype(datatype, constructors)
      solver.sort(sort.sortName)
    }

    private def mkFiniteSort(sort: Core.FiniteUniverseSort): Sort = {
      val datatype = solver.datatype(sort.sortName, 0)
      val constructors = (0 until sort.card).map { idx =>
        solver.constructor(getEnumName(idx, sort), Array.empty[String], Array.empty[Sort])
      }.toArray
      solver.declareDatatype(datatype, constructors)
      solver.sort(sort.sortName)
    }
      

    private def mkUnInterpretedSort(sort: Core.UnInterpretedSort)  = {
      solver.declareSort(sort.name, sort.numArgs)
      solver.sort(sort.sortName)
    }
    
    // API:     public void defineSort(String sort, Sort[] sortParams, Sort definition) throws SMTLIBException 
    private def mkAliasSort[S <: Core.Sort[S]](aliasSort: AliasSort[S]) = {
      val aliasName = aliasSort.name
      val aliasArgs = aliasSort.args
      val underlyingSort = aliasSort.underlyingSort
      solver.defineSort(aliasName, aliasArgs.toArray.map(x => lowerSort(x)), lowerSort(underlyingSort))
      solver.sort(aliasName)
    }

    override def lowerSort[A <: Core.Sort[A]](s: A): Sort =
      sortMap.get(s.box) match {
        case Some(sort) => sort
        case None =>
          s match {
            case _: Core.BoolSort => solver.sort(SMTLIBConstants.BOOL)
            case _: Core.NumericSort => solver.sort(SMTLIBConstants.INT)
            case arr @ Core.ArraySort(domainSort, rangeSort) =>
              solver.sort(SMTLIBConstants.ARRAY, lowerSort(domainSort), lowerSort(rangeSort))
            case srt: Core.UnInterpretedSort =>
              solver.sort(srt.sortName)
            case alias: Core.AliasSort[t] => unexpected(s"error: ${alias} sort undeclared")
            case dt: Core.DatatypeConstructorSort => unexpected(s"error: ${dt} sort undeclared")
            case finite: Core.FiniteUniverseSort => unexpected(s"error: ${finite} sort undeclared")
            case fun: Core.FunSort[?] => unexpected("cannot lower function sort in SMTInterpol backend", fun)
          }
      }

    override def defineSort[A <: Core.Sort[A]](s: A): Sort = {
      val lowered =
        sortMap.get(s) match {
          case Some(loweredSort) => loweredSort
          case None =>
            s match {
              case _: Core.BoolSort => lowerSort(s)
              case _: Core.NumericSort => lowerSort(s)
              case _: Core.ArraySort[x,y] => lowerSort(s)
              case uSort: Core.UnInterpretedSort =>
                val loweredSort = mkUnInterpretedSort(uSort)
                sortMap.update(uSort, loweredSort)
                loweredSort
              case aliasSort @ Core.AliasSort(_, _, _) =>
                val loweredSort = mkAliasSort(aliasSort)
                sortMap.update(aliasSort, loweredSort)
                loweredSort
              case dt: Core.DatatypeConstructorSort =>
                val loweredSort = mkDatatypeSort(dt)
                sortMap.update(dt, loweredSort)
                loweredSort
              case finite: Core.FiniteUniverseSort =>
                val loweredSort = mkFiniteSort(finite)
                sortMap.update(finite, loweredSort)
                loweredSort
              case fun: Core.FunSort[?] => unexpected(s"cannot define function sort in SMTInterpol backend: ${fun}")
            }
        }
      record(s"defineSort(${s.sortName})")
      lowered
    }

    override def defineConst[S <: Core.Sort[S]](value: Core.SortValue[S]): Term = {
      val lowered = lowerValue(value)
      record(s"defineConst(${value.toString})")
      lowered
    }

    private def mkFunction[S <: Core.Sort[S]](name: String, domain: List[Core.BoxedSort], range: S): FunctionSymbol =
      funMap.get(name) match {
        case Some(funcDef) => funcDef
        case None => 
          val domainSorts = domain.map(arg => lowerSort(arg.sort)).toArray
          val rangeSort = lowerSort(range)
          solver.declareFun(name, domainSorts, rangeSort)
          val fs = solver.getFunctionSymbol(name)
          funMap.update(name, fs)
          fs
      }

    override def declareVar[S <: Core.Sort[S]](name: String, sort: S): FunctionSymbol =
      sort match
        case funSort @ Core.FunSort(domainSort, rangeSort) =>
          mkFunction(name, funSort.domainSort, rangeSort)
        case _ =>
          funMap.getOrElseUpdate(name, {
            val lowered = lowerSort(sort)
            solver.declareFun(name, Array.empty, lowered)
            solver.getFunctionSymbol(name)
          })

    override def defineVar[S <: Core.Sort[S]](name: String, sort: S, expr: Core.Expr[S]): (FunctionSymbol, List[Term]) = {
      val decl = declareVar(name, sort)
      val axioms = sort match
        case funSort @ Core.FunSort(_, _) =>
          expr match
            case Core.Macro(_, args, body) =>
              val argVars = args.map { case (argName, argSort) =>
                solver.variable(argName, lowerSort(argSort.sort))
              }
              val bound = args.map(_._1).zip(argVars).toMap
              val bodyTerm = lower(bound, body)
              val retSort = lowerSort(body.sort)
              solver.defineFun(name, argVars.toArray, retSort, bodyTerm)
              funMap.update(name, solver.getFunctionSymbol(name))
              List()
            case Var(_, _) =>
              // When expr is a Var (uninterpreted or alias), no axiom needed
              List()
            case _ =>
              // For other function expressions, generate: forall args, name(args) = expr(args)
              val domainSorts = funSort.domainSort
              val rangeSort = funSort.rangeSort

              // Create fresh argument variables for the forall
              val args: List[(String, Core.BoxedSort)] =
                domainSorts.zipWithIndex.map { case (sort, idx) =>
                  (s"x$idx", sort)
                }

              // Build forall axiom: forall args, name(args) = expr(args)
              val forallAxiom = Core.mkForall(
                args,
                Core.mkEq(
                  Core.mkSubst("app", args.map(x => (x._1, Core.mkVar(x._1, x._2))), Core.mkVar(name, funSort)),
                  Core.mkSubst("app", args.map(x => (x._1, Core.mkVar(x._1, x._2))), expr)
                )
              )

              val loweredAxiom = lower(forallAxiom)
              solver.assertTerm(loweredAxiom)
              axiomsMap.update(name, loweredAxiom)
              List(loweredAxiom)
        case _ =>
          val symbolTerm = solver.term(name)
          val lowered = lower(expr)
          val equality = solver.term(SMTLIBConstants.EQUALS, symbolTerm, lowered)
          solver.assertTerm(equality)
          axiomsMap.update(name, equality)
          List(equality)
      record(s"defineVar($name)")
      (decl, axioms)
    }

    override def lowerValue[S <: Core.Sort[S]](value: Core.SortValue[S]): Term =
      value match
        case Core.SortValue.BoolValue(true) => solver.term(SMTLIBConstants.TRUE)
        case Core.SortValue.BoolValue(false) => solver.term(SMTLIBConstants.FALSE)
        case Core.SortValue.NumericValue(n) => solver.numeral(n.toString)
        case Core.SortValue.UnInterpretedValue(name, _) => solver.term(name)
        case Core.SortValue.AliasSortValue(name, _) => solver.term(name)
        case Core.SortValue.FiniteUniverseValue(index, sort) => solver.term(getEnumName(index, sort))
        case Core.SortValue.DatatypeValue(constructor, _) =>
          val constructorName = constructor.getName
          val args = constructor.getParams.map(param => lower(param.e)).toArray
          solver.term(constructorName, args *)
        case Core.SortValue.ArrayValue(default, _) =>
          lower(default)

    override def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): Term =
      exprMap.getOrElseUpdate(expr.box(), lower(Map.empty[String, TermVariable], expr))

    private def lower[S <: Core.Sort[S]](bound: Map[String, TermVariable], expr: Core.Expr[S]): Term =
      expr match
        case Core.Var(name, sort) =>
          sort match
            case _: Core.FunSort[?] => solver.term(name)
            case _ => bound.getOrElse(name, solver.term(name))
        case Core.Const(value) => lowerValue(value)
        case Core.ArraySelect(arrayExpr, indexExpr) =>
          solver.term(SMTLIBConstants.SELECT, lower(bound, arrayExpr), lower(bound, indexExpr))
        case Core.ArrayStore(arrayExpr, indexExpr, valueExpr) =>
          solver.term(SMTLIBConstants.STORE, lower(bound, arrayExpr), lower(bound, indexExpr), lower(bound, valueExpr))
        case Core.Top("ite", cond, thn, els, _) =>
          solver.term(SMTLIBConstants.ITE, lower(bound, cond), lower(bound, thn), lower(bound, els))
        case Core.Bop("=", lhs, rhs, _) =>
          solver.term(SMTLIBConstants.EQUALS, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop("=>", lhs, rhs, _) =>
          solver.term(SMTLIBConstants.IMPLIES, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop(op@(">" | ">=" | "<" | "<="), lhs, rhs, _) =>
          solver.term(op, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop("-", lhs, rhs, _) =>
          solver.term(SMTLIBConstants.MINUS, lower(bound, lhs), lower(bound, rhs))
        case Core.Uop("-", sub, _) => solver.term(SMTLIBConstants.MINUS, lower(bound, sub))
        case Core.Uop("not", sub, _) => solver.term(SMTLIBConstants.NOT, lower(bound, sub))
        case Core.Lop("and", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          solver.term(SMTLIBConstants.AND, loweredArgs *)
        case Core.Lop("or", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          solver.term(SMTLIBConstants.OR, loweredArgs *)
        case Core.Lop("+", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          solver.term(SMTLIBConstants.PLUS, loweredArgs *)
        case Core.Lop("*", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          solver.term(SMTLIBConstants.MUL, loweredArgs *)
        case Core.Forall(sortedArgs, body) =>
          val (vars, newBound) = wrapBinders(bound, sortedArgs)
          solver.quantifier(Script.FORALL, vars.toArray, lower(newBound, body), Array[Term]())
        case Core.Exists(sortedArgs, body) =>
          val (vars, newBound) = wrapBinders(bound, sortedArgs)
          solver.quantifier(Script.EXISTS, vars.toArray, lower(newBound, body), Array[Term]())
        case Core.Substitute("let", _, Core.Macro("letBody", _, _)) =>
          val eliminated = (new LetRemover()).visit(Core.emptyInterpEnv)(expr)
          lower(bound, eliminated)
        case Core.Substitute("app", bindings, bodyExpr) =>
          val bindingsEnv = bindings.toEnv
          bodyExpr match
            case Core.Macro(name, args, _) =>
              val concreteArgs = args.map { case (argName, _) =>
                bindingsEnv(argName) match
                  case Some(boundExpr) => lower(bound, boundExpr.e)
                  case None => unexpected(s"missing argument $argName when applying macro $name", expr)
              }
              solver.term(name, concreteArgs *)
            case Core.Var(name, _) =>
              val concreteArgs = bindings.map(_._2.e).map(arg => lower(bound, arg))
              solver.term(name, concreteArgs *)
            case other => unexpected("cannot apply non-function expression in SMTInterpol backend", other)
        case other =>
          unsupported(s"lower: unsupported SMTInterpol expression $other")

    
    private def wrapBinders(bound: Map[String, TermVariable],
                                   binders: List[(String, Core.BoxedSort)]): (List[TermVariable], Map[String, TermVariable]) = {
      val generated = binders.map { case (name, sort) =>
        val lowered = lowerSort(sort.sort)
        val termVar = solver.variable(name, lowered)
        (name, termVar)
      }
      val newBound = bound ++ generated
      (generated.map(_._2), newBound)
    }

    override def liftSort(sort: Sort): Core.BoxedSort =
      val sortName = sort.getName
      if sort.isArraySort then
        val indices = sort.getArguments
        if indices.length != 2 then
          unexpected(s"liftSort: array sort must have exactly 2 arguments, got ${indices.length}", sort)
        val domSort = liftSort(indices(0))
        val rangeSort = liftSort(indices(1))
        Core.arraySort(domSort, rangeSort)
      else if sortName == SMTLIBConstants.BOOL then
        Core.BoolSort().box
      else if sortName == SMTLIBConstants.INT then
        Core.NumericSort().box
      else
        // Check in type environment for user-defined sorts
        typeEnv.lookup(sortName).getOrElse {
          // Could be uninterpreted or datatype
          Core.UnInterpretedSort(sortName, 0).box
        }

    override def liftTerm(term: Term): Core.BoxedExpr =
      import de.uni_freiburg.informatik.ultimate.logic.*

      term match
        case constTerm: ConstantTerm =>
          val value = constTerm.getValue
          value match
            case rat: Rational =>
              if rat.isIntegral then
                Core.mkConst(rat.numerator.intValue())
              else
                // For now, treat as integer (truncate)
                Core.mkConst(rat.numerator.divide(rat.denominator).intValue())
            case bigInt: java.math.BigInteger =>
              Core.mkConst(bigInt.intValue())
            case bigDec: java.math.BigDecimal =>
              Core.mkConst(bigDec.intValue())
            case _ =>
              unsupported(s"liftTerm: unsupported constant value type: ${value.getClass}")

        case termVar: TermVariable =>
          val name = termVar.getName
          val sort = liftSort(termVar.getSort)
          Core.mkVar(name, sort).box()

        case qf: QuantifiedFormula =>
          val isForall = (qf.getQuantifier == Script.FORALL)
          val vars = qf.getVariables.map { v =>
            val name = v.getName
            val sort = liftSort(v.getSort)
            (name, sort)
          }.toList
          val body = liftTerm(qf.getSubformula)
          body.unify(Core.BoolSort()) match
            case Some(unifiedBody) =>
              if isForall then
                Core.mkForall(vars, unifiedBody).box()
              else
                Core.mkExists(vars, unifiedBody).box()
            case None =>
              unexpected(s"liftTerm: quantifier body is not boolean: $body", term)

        case appTerm: ApplicationTerm =>
          val func = appTerm.getFunction
          val params = appTerm.getParameters.map(liftTerm)

          // Handle built-in operators
          if func.isIntern then
            val funcName = func.getName
            funcName match
              case SMTLIBConstants.TRUE =>
                Core.mkConst(true)

              case SMTLIBConstants.FALSE =>
                Core.mkConst(false)

              case SMTLIBConstants.NOT =>
                if params.length != 1 then
                  unexpected(s"liftTerm: NOT expects 1 parameter, got ${params.length}", term)
                params(0).unify(Core.BoolSort()) match
                  case Some(unifiedParam) => Core.mkNot(unifiedParam).box()
                  case None => unexpected(s"liftTerm: NOT parameter is not boolean", term)

              case SMTLIBConstants.AND =>
                Core.unifyTerms(params.toList, Core.BoolSort()) match
                  case Some(unified) => Core.mkAnd(unified).box()
                  case None => unexpected(s"liftTerm: AND parameters type mismatch", term)

              case SMTLIBConstants.OR =>
                Core.unifyTerms(params.toList, Core.BoolSort()) match
                  case Some(unified) => Core.mkOr(unified).box()
                  case None => unexpected(s"liftTerm: OR parameters type mismatch", term)

              case SMTLIBConstants.IMPLIES =>
                if params.length != 2 then
                  unexpected(s"liftTerm: IMPLIES expects 2 parameters, got ${params.length}", term)
                (params(0).unify(Core.BoolSort()), params(1).unify(Core.BoolSort())).tupled match
                  case Some(unifiedPremise, unifiedConclusion) =>
                    Core.mkImplies(unifiedPremise, unifiedConclusion).box()
                  case None =>
                    unexpected(s"liftTerm: IMPLIES type mismatch", term)

              case SMTLIBConstants.EQUALS =>
                if params.length != 2 then
                  unexpected(s"liftTerm: EQUALS expects 2 parameters, got ${params.length}", term)
                val lhs = params(0)
                val rhs = params(1)
                rhs.e.unify(lhs.sort) match
                  case Some(unifiedRhs) => Core.mkEq(lhs.e, unifiedRhs).box()
                  case None => unexpected(s"liftTerm: EQUALS type mismatch: $lhs vs $rhs", term)

              case SMTLIBConstants.ITE =>
                if params.length != 3 then
                  unexpected(s"liftTerm: ITE expects 3 parameters, got ${params.length}", term)
                val cond = params(0)
                val thn = params(1)
                val els = params(2)
                (cond.unify(Core.BoolSort()), thn.unify(els.sort)).tupled match
                  case Some(unifiedCond, unifiedThn) =>
                    Core.mkIte(unifiedCond, unifiedThn, els.e).box()
                  case None =>
                    unexpected(s"liftTerm: ITE type mismatch", term)

              case SMTLIBConstants.PLUS =>
                Core.unifyTerms(params.toList, Core.NumericSort()) match
                  case Some(unified) => Core.mkAdd(unified).box()
                  case None => unexpected(s"liftTerm: PLUS parameters type mismatch", term)

              case SMTLIBConstants.MINUS =>
                if params.length == 1 then
                  // Unary minus (negation)
                  params(0).unify(Core.NumericSort()) match
                    case Some(unifiedParam) => Core.mkNegative(unifiedParam).box()
                    case None => unexpected(s"liftTerm: MINUS parameter is not numeric", term)
                else if params.length == 2 then
                  // Binary minus (subtraction)
                  (params(0).unify(Core.NumericSort()), params(1).unify(Core.NumericSort())).tupled match
                    case Some(unifiedLhs, unifiedRhs) =>
                      Core.mkMinus(unifiedLhs, unifiedRhs).box()
                    case None =>
                      unexpected(s"liftTerm: MINUS type mismatch", term)
                else
                  unexpected(s"liftTerm: MINUS expects 1 or 2 parameters, got ${params.length}", term)

              case SMTLIBConstants.MUL =>
                Core.unifyTerms(params.toList, Core.NumericSort()) match
                  case Some(unified) => Core.mkMul(unified).box()
                  case None => unexpected(s"liftTerm: MUL parameters type mismatch", term)

              case "<" | "<=" | ">" | ">=" =>
                if params.length != 2 then
                  unexpected(s"liftTerm: comparison expects 2 parameters, got ${params.length}", term)
                (params(0).unify(Core.NumericSort()), params(1).unify(Core.NumericSort())).tupled match
                  case Some(unifiedLhs, unifiedRhs) =>
                    Core.mkBop(funcName, unifiedLhs, unifiedRhs, Core.boolSort).box()
                  case None =>
                    unexpected(s"liftTerm: comparison type mismatch", term)

              case SMTLIBConstants.SELECT =>
                if params.length != 2 then
                  unexpected(s"liftTerm: SELECT expects 2 parameters, got ${params.length}", term)
                val arr = params(0)
                val idx = params(1)
                arr.sort match
                  case arrSort@Core.ArraySort(_, _) =>
                    arr.unify(Core.ArraySort(idx.sort, arrSort.rangeSort)) match
                      case Some(unifiedArr) =>
                        Core.mkSelect(unifiedArr, idx.e).box()
                      case None =>
                        unexpected(s"liftTerm: SELECT index type mismatch", term)
                  case _ =>
                    unexpected(s"liftTerm: SELECT on non-array: ${arr.sort}", term)

              case SMTLIBConstants.STORE =>
                if params.length != 3 then
                  unexpected(s"liftTerm: STORE expects 3 parameters, got ${params.length}", term)
                val arr = params(0)
                val idx = params(1)
                val value = params(2)
                arr.unify(Core.ArraySort(idx.sort, value.sort)) match
                  case Some(unifiedArr) =>
                    Core.mkStore(unifiedArr, idx.e, value.e).box()
                  case None =>
                    unexpected(s"liftTerm: STORE type mismatch", term)

              case "const" =>
                // Constant array: (const value)
                if params.length != 1 then
                  unexpected(s"liftTerm: const array expects 1 parameter, got ${params.length}", term)
                val value = params(0)
                val arraySort = liftSort(term.getSort)
                arraySort.sort match
                  case arr@Core.ArraySort(_, _) =>
                    value.unify(arr.rangeSort) match
                      case Some(unifiedValue) =>
                        Core.mkConstArray(arr.domainSort, unifiedValue)
                      case None =>
                        unexpected(s"liftTerm: const array value type mismatch", term)
                  case _ =>
                    unexpected(s"liftTerm: const array has non-array sort $arraySort", term)

              case _ =>
                unsupported(s"liftTerm: unsupported internal function: $funcName")

          else
            // User-defined or uninterpreted function
            val funcName = func.getName
            val funcSort = func.getReturnSort
            val retSort = liftSort(funcSort)

            if params.isEmpty then
              // Nullary function (constant)
              interpEnv.lookup(funcName) match
                case Some(expr: BoxedExpr) => expr
                case None => Core.mkVar(funcName, retSort).box()
            else
              // Function application
              val domainSorts = func.getParameterSorts.toList.map(liftSort)
              val funSort = Core.funSort(domainSorts, retSort)

              interpEnv.lookup(funcName) match
                case Some(funcExpr) =>
                  funcExpr.unify(funSort) match {
                    case Some(_) =>
                      val func = Core.mkVar(funcName, funSort)
                      val bindings = params.zipWithIndex.map { case (arg, i) =>
                        (s"arg_$i", arg)
                      }.toList
                      Core.mkSubst("app", bindings, func).box()
                    case None => unexpected(s"function ${funcName} has a different sort ${funSort} in SmtInterpol", funSort)
                  }

                case None =>
                  // Undeclared function - create application
                  val func = Core.mkVar(funcName, funSort)
                  interpEnv.add(funcName, func)
                  val bindings = params.zipWithIndex.map { case (arg, i) =>
                    (s"arg_$i", arg)
                  }.toList
                  Core.mkSubst("app", bindings, func).box()
        case _ =>
          unsupported(s"liftTerm: unsupported term type: ${term.getClass.getSimpleName}")

    override def liftFunc(func: FunctionSymbol): Core.BoxedExpr =
      val name = func.getName
      interpEnv.lookup(name).getOrElse {
        val retSort = liftSort(func.getReturnSort)
        val paramSorts = func.getParameterSorts.map(liftSort).toList
        if paramSorts.isEmpty then
          Core.mkVar(name, retSort).box()
        else
          val funSort = Core.funSort(paramSorts.map(_.box), retSort)
          Core.mkVar(name, funSort).box()
      }

    private def parseLogic(logics: SmtSolver.Logic): Logics = {
      // Arithmetic, Quantifier, Datatype+Arrays
      logics match {
        case (SmtSolver.Arith.NIA, true, true) => Logics.AUFDTNIA
        case (SmtSolver.Arith.NIA, true, false) => Logics.UFNIA
        case (SmtSolver.Arith.NIA, false, false) => Logics.QF_UFNIA
        case (SmtSolver.Arith.NIA, false, true) => Logics.QF_AUFNIA
        case (SmtSolver.Arith.LIA, true, true) => Logics.AUFDTLIA
        case (SmtSolver.Arith.LIA, true, false) => Logics.UFLIA
        case (SmtSolver.Arith.LIA, false, true) => Logics.QF_AUFLIA
        case (SmtSolver.Arith.LIA, false, false) => Logics.QF_UFLIA
        case (SmtSolver.Arith.NoArith, true, true) => Logics.ALL
        case (SmtSolver.Arith.NoArith, true, false) => Logics.UF
        case (SmtSolver.Arith.NoArith, false, true) => Logics.QF_AUFLIA
        case (SmtSolver.Arith.NoArith, false, false) => Logics.QF_UF
      }
    }

    override def lookupDecl[S <: Core.Sort[S]](v: String, s: S): Option[LoweredVarDecl] = {
      try
        Some(funMap(v))
      catch
        case _ => None
    }

    override def initialize(logicOptions: SmtSolver.Logic): Unit = {
      val targetLogic = Logics.ALL // TODO
      val targetLogicName = targetLogic.toString
      solver.reset()
      solver.setOption(":produce-proofs", true)
      solver.setOption(":produce-models", true)
      solver.setLogic(targetLogicName)
      activeLogic = Some(targetLogicName)

      typeEnv.registerUpdateHook { (name, sort) =>
        val lowered = defineSort(sort.sort)
        s"defineSort $name: ${lowered.toString}"
      }

      interpEnv.registerUpdateHook { (name, expr) =>
        val (decl, _) = defineVar(name, expr.sort, expr.e)
        s"defineVar $name: ${decl.toString}"
      }

      typeEnv.foreach { case (_, sort) => ignore(defineSort(sort.sort)) }
      interpEnv.foreach { case (name, boxedExpr) => ignore(defineVar(name, boxedExpr.sort, boxedExpr.e)) }

      record(s"initialize($targetLogicName)")
    }

    override def add(fs: List[Core.BoxedExpr]): List[Term] = {
      val lowered = fs.map(expr => lower(expr.e))
      lowered.foreach(solver.assertTerm)
      record(s"add(${fs.map(_.toString).mkString(",")})")
      lowered
    }

    override def addTerms(terms: List[Term]): List[Term] = {
      terms.foreach(solver.assertTerm)
      record(s"addTerms(${terms.map(_.toString).mkString(",")})")
      terms
    }

    override def push(): Unit = solver.push(1)

    override def pop(): Unit = solver.pop(1)

    override def reset(): Unit = {
      solver.reset()
      funMap.clear()
      sortMap.clear()
      exprMap.clear()
      axiomsMap.clear()
      activeLogic.foreach(solver.setLogic)
      typeEnv.foreach { case (_, sort) => ignore(defineSort(sort.sort)) }
      interpEnv.foreach { case (name, boxedExpr) => ignore(defineVar(name, boxedExpr.sort, boxedExpr.e)) }
      record("reset()")
    }

    override def fork(): SmtInterpolSolver = new SmtInterpolSolver(typeEnv.copy(), interpEnv.copy())

    override def getModel: Option[SmtSolver.Model[Term, FunctionSymbol]] =
      Option(solver.getModel).map(model => new SMTInterpolModel(model, this))

    override def getUnsatCore: Option[SmtSolver.UnsatCore[Term, FunctionSymbol]] = {
      try {
        val coreTerms = solver.getUnsatCore
        Some(SMTInterpolUnsatCore(coreTerms.toSet, this))
      } catch {
        case _ => None
      }
    }

    override def checkSat(): SmtSolver.Result =
      solver.checkSat() match {
        case Script.LBool.SAT => SmtSolver.Result.SAT
        case Script.LBool.UNSAT => SmtSolver.Result.UNSAT
        case _ => SmtSolver.Result.UNKNOWN
      }
  }

  class SMTInterpolUnsatCore(coreTerms: Set[Term], solver: SmtInterpolSolver) extends SmtSolver.UnsatCore[Term, FunctionSymbol](solver) {

    override def terms(): Set[Term] = coreTerms

    override def formulas(): Set[Expr[BoolSort]] =
      coreTerms.map(x => solver.liftTerm(x).unify(Core.BoolSort()).get)
  }

  class SMTInterpolModel(model: de.uni_freiburg.informatik.ultimate.logic.Model,
                         solver: SmtInterpolSolver)
    extends SmtSolver.Model[Term, FunctionSymbol](solver) {

    override def formula(): Core.Expr[Core.BoolSort] = {
      val term = asTerm()
      val expr = solver.liftTerm(term)
      expr.unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"SMTInterpolModel.formula(): Expression constructed from model is ${expr}, which does not return a boolean.")
      }
    }

    override def valueOf[S <: Core.Sort[S]](name: String, sort: S): Option[Core.Expr[S]] = {
      val someExpr = evaluate(Core.mkVar(name, sort))
      someExpr.unify(sort) match {
        case Some(unifiedExpr) => Some(unifiedExpr)
        case None => None
      }
    }

    override def vocabulary(): (List[Core.BoxedSort], List[String]) = {
      val definedFunctions = model.getDefinedFunctions.toArray(new Array[FunctionSymbol](0))
      val constNames = definedFunctions
        .filter(fs => fs.getParameterSorts.isEmpty)
        .map(fs => fs.getName)
        .toList
      val sorts = definedFunctions
        .filter(fs => fs.getParameterSorts.isEmpty)
        .map(fs => solver.liftSort(fs.getReturnSort))
        .toList
      (sorts, constNames)
    }

    override def evaluate[S <: Core.Sort[S]](expr: Core.Expr[S]): Core.Expr[S] = {
      val term = solver.lower(expr)
      val evaluatedTerm = model.evaluate(term)
      solver.liftTerm(evaluatedTerm).unify(expr.sort) match {
        case Some(unified) => unified
        case None => unexpected(s"model evaluator in SmtInterpolSolver: got term ${evaluatedTerm} but it is not of sort ${expr.sort}")
      }
    }

    override def asNegatedTerm(): Term = {
      val term = asTerm()
      solver.getSolver.term(SMTLIBConstants.NOT, term)
    }

    override def asTerm(): Term = modelToTerm

    override def formula(vocab: Set[(String, BoxedSort)]): Expr[BoolSort] = {
      val term = asTerm(vocab)
      val expr = solver.liftTerm(term)
      expr.unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"SMTInterpolModel.formula(vocab): Expression constructed from model is ${expr}, which does not return a boolean.")
      }
    }

    override def asNegatedTerm(vocab: Set[(String, BoxedSort)]): Term =
      val tt = asTerm(vocab)
      solver.getSolver.term(SMTLIBConstants.NOT, tt)


    def modelToTerm: Term = {
      val assignments = model
        .getDefinedFunctions
        .toArray(new Array[FunctionSymbol](0))
        .iterator
        .flatMap(termOfSymbol)
        .toArray

      assignments.length match
        case 0 =>
          solver.getSolver.term(SMTLIBConstants.TRUE)
        case 1 =>
          assignments(0)
        case _ =>
          solver.getSolver.term(SMTLIBConstants.AND, assignments *)
    }

    private def termOfSymbol(fs: FunctionSymbol): Option[Term] = {
      // Skip internal helper symbols that already have built-in definitions.
      if (fs.isIntern && fs.getDefinition != null) then
        None
      else
        val vars = freshVariables(fs.getParameterSorts)
        val lhs = applySymbol(fs, vars.map(identity[Term]))
        val rhs = model.getFunctionDefinition(fs.getName, vars)
        val eq = solver.getSolver.term(SMTLIBConstants.EQUALS, lhs, rhs)
        val quantified =
          if vars.isEmpty then eq
          else solver.getSolver.quantifier(Script.FORALL, vars, eq)
        Some(quantified)
    }

    private def freshVariables(paramSorts: Array[Sort]): Array[TermVariable] = {
      var counter = 0
      val vars = new Array[TermVariable](paramSorts.length)
      while counter < paramSorts.length do
        val name = s"@m$counter"
        vars(counter) = solver.getSolver.variable(name, paramSorts(counter))
        counter += 1
      vars
    }

    private def applySymbol(fs: FunctionSymbol, args: Array[Term]): Term = {
      val indices = fs.getIndices
      val returnSort: Sort | Null =
        if fs.isReturnOverload then fs.getReturnSort
        else null

      solver.getSolver.term(fs.getName, indices, returnSort, args *)
    }


    override def asTerm(vocabulary: Set[(String, BoxedSort)]): Term = {
      val equalities = vocabulary.map { case (name, sort) =>
        println(s"asTerm: enumerating ${name} : ${sort} ...")

        sort.sort match {
          case fs: Core.FunSort[t] =>
            val funcSym = solver.lookupDecl(name, sort).get
            val t = this.termOfSymbol(funcSym).get
            t
          case _ =>
            val c = solver.getSolver.term(name)
            val value = model.evaluate(c)
            solver.getSolver.term(SMTLIBConstants.EQUALS, c, value)
        }
      }.toList

      equalities match {
        case Nil => solver.getSolver.term(SMTLIBConstants.TRUE)
        case List(single) => single
        case _ => solver.getSolver.term(SMTLIBConstants.AND, equalities.toArray *)
      }
    }

    override def apply(arg: String, sort: Core.BoxedSort): Option[BoxedExpr] = {
      Some(solver.liftTerm(model.evaluate(solver.getSolver.term(arg))))
    }
  }
}
