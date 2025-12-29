package tempura.smt

import io.github.cvc5.{Datatype, DatatypeConstructorDecl, DatatypeDecl, Kind, Solver, Sort as Cvc5Sort, Term as Cvc5Term, TermManager}
import tempura.expression.Core.*
import tempura.helpers.Utils.*
import cats.implicits.*
import tempura.expression.Core
import tempura.expression.transforms.LetRemover

import scala.collection.mutable
import scala.reflect.ClassTag

object Cvc5Solver {

  def apply(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv): Cvc5Solver =
    new Cvc5Solver(typeEnv, interpEnv)

  final class Cvc5Solver(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)
    extends SmtSolver.Solver[Cvc5Term, Cvc5Term](typeEnv, interpEnv) {

    override type LoweredSort = Cvc5Sort

    private val termManager = new TermManager()
    private val solver = new Solver(termManager)

    private val sortMap: mutable.Map[Core.BoxedSort, Cvc5Sort] = mutable.Map()
    private val exprMap: mutable.Map[Core.BoxedExpr, Cvc5Term] = mutable.Map()
    private val funcMap: mutable.Map[String, Cvc5Term] = mutable.Map()
    private val constMap: mutable.Map[String, Cvc5Term] = mutable.Map()
    private val datatypeCtorMap: mutable.Map[(String, String), Cvc5Term] = mutable.Map()

    private given ClassTag[Cvc5Term] = ClassTag(classOf[Cvc5Term])

    private given ClassTag[Cvc5Sort] = ClassTag(classOf[Cvc5Sort])

    private var history: List[String] = Nil

    private def record(entry: String): Unit = history = entry :: history

    override def getHistory: List[String] = history

    def getSolver: Solver = solver

    def getTermManager: TermManager = termManager

    def declaredConstants: Map[String, Cvc5Term] = constMap.toMap

    def declaredFunctions: Map[String, Cvc5Term] = funcMap.toMap

    def lookupDatatypeConstructor(sort: String, constructor: String): Option[Cvc5Term] =
      datatypeCtorMap.get((sort, constructor))

    private def cacheDatatypeConstructors(sortName: String, sort: Cvc5Sort): Unit = {
      if sort.isDatatype then
        val datatype: Datatype = sort.getDatatype
        (0 until datatype.getNumConstructors).foreach { idx =>
          val ctor = datatype.getConstructor(idx)
          datatypeCtorMap.update((sortName, ctor.getName), ctor.getTerm)
        }
    }

    override def lowerSort[S <: Core.Sort[S]](sort: S): Cvc5Sort =
      sortMap.get(sort.box) match {
        case Some(s) => s
        case None =>
          sort match {
            case _: Core.NumericSort => termManager.getIntegerSort
            case _: Core.BoolSort => termManager.getBooleanSort
            case _@Core.ArraySort(dom, range) =>
              val loweredDom = lowerSort(dom)
              val loweredRange = lowerSort(range)
              termManager.mkArraySort(loweredDom, loweredRange)
            case _ => unexpected(s"error: undeclared sort ${sort.toString}")
          }
      }

    override def defineSort[A <: Sort[A]](sort: A): Cvc5Sort = {
      record(s"defineSort(${sort.sortName})")
      sortMap.get(sort.box) match {
        case Some(s) => s
        case None =>
          sort match {
            case _: Core.NumericSort => termManager.getIntegerSort
            case _: Core.BoolSort => termManager.getBooleanSort
            case arr@Core.ArraySort(domainSort, rangeSort) =>
              val domain = lowerSort(domainSort)
              val range = lowerSort(rangeSort)
              val a = termManager.mkArraySort(domain, range)
              sortMap.update(sort, a)
              a
            case u: Core.UnInterpretedSort =>
              val a = solver.declareSort(u.sortName, u.numArgs)
              sortMap.update(sort, a)
              a
            case alias: Core.AliasSort[_] =>
              termManager.mkUninterpretedSort(alias.sortName)
            case finite: Core.FiniteUniverseSort =>
              val a = mkFiniteSort(finite)
              sortMap.update(sort, a)
              a
            case dt: Core.DatatypeConstructorSort =>
              val a = mkDatatypeSort(dt)
              sortMap.update(sort, a)
              a
            case fun: Core.FunSort[_] => unexpected("cannot lower function sorts in CVC5 backend", fun)
          }
      }
    }

    private def mkDatatypeSort(sort: Core.DatatypeConstructorSort): Cvc5Sort = {
      sortMap.get(sort.box) match
        case Some(existing) => existing
        case None =>
          val datatypeDecl: DatatypeDecl = termManager.mkDatatypeDecl(sort.sortName)
          sort.constructors.foreach { constructor =>
            val ctorDecl: DatatypeConstructorDecl = termManager.mkDatatypeConstructorDecl(constructor.name)
            constructor.args.foreach { case (fieldName, boxedSort) =>
              val fieldSort = boxedSort.sort
              if fieldSort == sort then
                ctorDecl.addSelectorSelf(fieldName)
              else
                ctorDecl.addSelector(fieldName, lowerSort(fieldSort))
            }
            datatypeDecl.addConstructor(ctorDecl)
          }
          val lowered = termManager.mkDatatypeSort(datatypeDecl)
          sortMap.update(sort.box, lowered)
          cacheDatatypeConstructors(sort.sortName, lowered)
          lowered
    }

    private def mkFiniteSort(sort: Core.FiniteUniverseSort): Cvc5Sort = {
      sortMap.getOrElseUpdate(sort.box, {
        val decl = termManager.mkDatatypeDecl(sort.sortName)
        (0 until sort.card).foreach { idx =>
          val ctorDecl = termManager.mkDatatypeConstructorDecl(getEnumName(idx, sort))
          decl.addConstructor(ctorDecl)
        }
        val lowered = termManager.mkDatatypeSort(decl)
        cacheDatatypeConstructors(sort.sortName, lowered)
        lowered
      })
    }

    override def defineConst[S <: Core.Sort[S]](value: Core.SortValue[S]): Cvc5Term = lowerValue(value)

    override def declareVar[S <: Core.Sort[S]](name: String, sort: S): Cvc5Term =
      sort match
        case funSort@Core.FunSort(dom, rangeSort) =>
          funcMap.getOrElseUpdate(name, {
            val domain = dom.map(arg => lowerSort(arg.sort))
            val range = lowerSort(rangeSort)
            solver.declareFun(name, domain.toArray, range)
          })
        case _ =>
          constMap.getOrElseUpdate(name, {
            val loweredSort = lowerSort(sort)
            termManager.mkConst(loweredSort, name)
          })

    override def defineVar[S <: Core.Sort[S]](name: String, sort: S, expr: Core.Expr[S]): (Cvc5Term, List[Cvc5Term]) = {
      val symbol = declareVar(name, sort)
      val axioms = sort match
        case funSort: Core.FunSort[t] =>
          expr match {
            case Core.Macro(_, args, body) =>
              val argTerms = args.map { case (argName, boxedSort) =>
                termManager.mkVar(lowerSort(boxedSort.sort), argName)
              }
              val localBound = args.map(_._1).zip(argTerms).toMap
              val bodyTerm = lower(localBound, body)
              val application = termManager.mkTerm(Kind.APPLY_UF, (symbol +: argTerms).toArray)
              val equality = termManager.mkTerm(Kind.EQUAL, application, bodyTerm)
              val binder = termManager.mkTerm(Kind.VARIABLE_LIST, argTerms.toArray)
              val forall = termManager.mkTerm(Kind.FORALL, binder, equality)
              solver.assertFormula(forall)
              List(forall)
            case _: Core.Var[?] => List()
            case other =>

              val args = funSort.domainSort.zipWithIndex map { case (boxedSort, argIndex) =>
                val argName = s"x_$argIndex"
                (argName, termManager.mkVar(lowerSort(boxedSort.sort), argName))
              }

              val localBound = args.toMap
              val bodyTerm = lower(localBound, other)
              val application = termManager.mkTerm(Kind.APPLY_UF, (symbol +: args.map(x => x._2)).toArray)
              val equality = termManager.mkTerm(Kind.EQUAL, application, bodyTerm)
              val binder = termManager.mkTerm(Kind.VARIABLE_LIST, args.map(x => x._2).toArray)
              val forall = termManager.mkTerm(Kind.FORALL, binder, equality)
              solver.assertFormula(forall)
              List(forall)

            // val lowered = lower(other)
            // val eq = termManager.mkTerm(Kind.EQUAL, symbol, lowered)
            // solver.assertFormula(eq)
            // List(eq)
          }
        case _ =>
          val lowered = lower(expr)
          val eq = termManager.mkTerm(Kind.EQUAL, symbol, lowered)
          solver.assertFormula(eq)
          List(eq)
      record(s"defineVar($name)")
      (symbol, axioms)
    }

    override def lowerValue[S <: Core.Sort[S]](value: Core.SortValue[S]): Cvc5Term =
      value match
        case Core.SortValue.BoolValue(flag) =>
          if flag then
            termManager.mkTrue()
          else
            termManager.mkFalse()
        case Core.SortValue.NumericValue(n) =>
          termManager.mkInteger(n.toLong)
        case Core.SortValue.UnInterpretedValue(name, sort) =>
          declareVar(name, sort)
        case Core.SortValue.ArrayValue(default, arrSort) =>
          val defaultTerm = lower(default)
          termManager.mkConstArray(lowerSort(arrSort.domainSort), defaultTerm)
        case Core.SortValue.FiniteUniverseValue(index, finite) =>
          val lowered = mkFiniteSort(finite)
          val ctorName = getEnumName(index, finite)
          datatypeCtorMap.getOrElse((finite.name, ctorName),
            unexpected(s"constructor ${ctorName} missing for finite sort ${finite.name}", finite))
        case Core.SortValue.DatatypeValue(inst, datatypeSort) =>
          val lowered = mkDatatypeSort(datatypeSort)
          val ctorName = inst.getName
          val ctor = datatypeCtorMap.getOrElse((datatypeSort.sortName, ctorName),
            unexpected(s"constructor ${ctorName} missing for datatype ${datatypeSort.sortName}", datatypeSort))
          val args = inst.getParams.map(param => lower(param.e))
          if args.isEmpty then ctor else termManager.mkTerm(Kind.APPLY_CONSTRUCTOR, (ctor +: args).toArray)
        case Core.SortValue.AliasSortValue(name, sort) => termManager.mkConst(lowerSort(sort), name)

    override def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): Cvc5Term =
      exprMap.getOrElseUpdate(expr.box(), lower(Map.empty[String, Cvc5Term], expr))

    private def lower[S <: Core.Sort[S]](bound: Map[String, Cvc5Term], expr: Core.Expr[S]): Cvc5Term =
      expr match
        case Core.Var(name, _) => bound.getOrElse(name, declareVar(name, expr.sort))
        case Core.Const(value) => lowerValue(value)
        case Core.ArraySelect(arr, idx) =>
          termManager.mkTerm(Kind.SELECT, lower(bound, arr), lower(bound, idx))
        case Core.ArrayStore(arr, idx, value) =>
          termManager.mkTerm(Kind.STORE, lower(bound, arr), lower(bound, idx), lower(bound, value))
        case Core.Top("ite", cond, thn, els, _) =>
          termManager.mkTerm(Kind.ITE, lower(bound, cond), lower(bound, thn), lower(bound, els))
        case Core.Bop("=", lhs, rhs, _) =>
          termManager.mkTerm(Kind.EQUAL, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop("=>", lhs, rhs, _) =>
          termManager.mkTerm(Kind.IMPLIES, lower(bound, lhs), lower(bound, rhs))
        case Core.Top("=>", premise, thn, els, _) =>
          termManager.mkTerm(Kind.ITE, lower(bound, premise), lower(bound, thn), lower(bound, els))
        case Core.Bop(op@(">" | ">=" | "<" | "<="), lhs, rhs, _) =>
          val kind = op match
            case ">" => Kind.GT
            case ">=" => Kind.GEQ
            case "<" => Kind.LT
            case "<=" => Kind.LEQ
          termManager.mkTerm(kind, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop("-", lhs, rhs, _) =>
          termManager.mkTerm(Kind.SUB, lower(bound, lhs), lower(bound, rhs))
        case Core.Bop("/", lhs, rhs, _) =>
          termManager.mkTerm(Kind.INTS_DIVISION, lower(bound, lhs), lower(bound, rhs))
        case Core.Uop("-", sub, _) => termManager.mkTerm(Kind.NEG, lower(bound, sub))
        case Core.Uop("not", sub, _) => termManager.mkTerm(Kind.NOT, lower(bound, sub))
        case Core.Lop("and", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          termManager.mkTerm(Kind.AND, loweredArgs.toArray)
        case Core.Lop("or", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          termManager.mkTerm(Kind.OR, loweredArgs.toArray)
        case Core.Lop("+", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          termManager.mkTerm(Kind.ADD, loweredArgs.toArray)
        case Core.Lop("*", args, _, _) =>
          val loweredArgs = args.map(arg => lower(bound, arg))
          termManager.mkTerm(Kind.MULT, loweredArgs.toArray)
        case Core.Bop("at-most", Core.Const(Core.SortValue.NumericValue(limit)), Core.Lop("at-most", args, _, _), _) =>
          val indicators = args.map { arg =>
            val lowered = lower(bound, arg)
            termManager.mkTerm(Kind.ITE, lowered, termManager.mkInteger(1), termManager.mkInteger(0))
          }
          val sum =
            indicators match
              case Nil => termManager.mkInteger(0)
              case head :: tail =>
                tail.foldLeft(head) { (acc, next) =>
                  termManager.mkTerm(Kind.ADD, acc, next)
                }
          termManager.mkTerm(Kind.LEQ, sum, termManager.mkInteger(limit))
        case Core.Bop("at-least", Core.Const(Core.SortValue.NumericValue(limit)), Core.Lop("at-least", args, _, _), _) =>
          val indicators = args.map { arg =>
            val lowered = lower(bound, arg)
            termManager.mkTerm(Kind.ITE, lowered, termManager.mkInteger(1), termManager.mkInteger(0))
          }
          val sum =
            indicators match
              case Nil => termManager.mkInteger(0)
              case head :: tail =>
                tail.foldLeft(head) { (acc, next) =>
                  termManager.mkTerm(Kind.ADD, acc, next)
                }
          termManager.mkTerm(Kind.GEQ, sum, termManager.mkInteger(limit))
        case Core.Forall(sortedArgs, body) =>
          val (binders, newBound) = instantiateBinders(bound, sortedArgs)
          val binder = termManager.mkTerm(Kind.VARIABLE_LIST, binders.toArray)
          val bodyTerm = lower(newBound, body)
          termManager.mkTerm(Kind.FORALL, binder, bodyTerm)
        case Core.Exists(sortedArgs, body) =>
          val (binders, newBound) = instantiateBinders(bound, sortedArgs)
          val binder = termManager.mkTerm(Kind.VARIABLE_LIST, binders.toArray)
          val bodyTerm = lower(newBound, body)
          termManager.mkTerm(Kind.EXISTS, binder, bodyTerm)
        case Core.Substitute("let", _, Core.Macro("letBody", _, _)) =>
          val eliminated = (new LetRemover()).visit(Core.emptyInterpEnv)(expr)
          lower(bound, eliminated)
        case Core.Substitute("app", bindings, bodyExpr) =>
          val bindingsEnv = bindings.toEnv
          bodyExpr match
            case Core.Macro(name, args, _) =>
              val funTerm = declareFunction(name, args.map(_._2), bodyExpr.sort)
              val loweredArgs = args.map { case (argName, _) =>
                bindingsEnv(argName) match
                  case Some(boundExpr) => lower(bound, boundExpr.e)
                  case None => unexpected(s"missing argument $argName when applying macro $name", expr)
              }
              termManager.mkTerm(Kind.APPLY_UF, (funTerm +: loweredArgs).toArray)
            case Core.Var(name, _) =>
              val funTerm = funcMap.getOrElse(name, declareVar(name, bodyExpr.sort))
              val loweredArgs = bindings.map(_._2.e).map(arg => lower(bound, arg))
              termManager.mkTerm(Kind.APPLY_UF, (funTerm +: loweredArgs).toArray)
            case _ => unexpected("cannot apply non-function expression in CVC5 backend", expr)
        case other => unsupported(s"expression lowering not implemented for ${other}")

    private def instantiateBinders(bound: Map[String, Cvc5Term],
                                   binders: List[(String, Core.BoxedSort)]): (List[Cvc5Term], Map[String, Cvc5Term]) = {
      val generated = binders.map { case (name, sort) =>
        val lowered = lowerSort(sort.sort)
        val term = termManager.mkVar(lowered, name)
        (name, term)
      }
      val newBound = bound ++ generated
      (generated.map(_._2), newBound)
    }

    private def declareFunction[A <: Core.Sort[A]](name: String,
                                                   domain: List[Core.BoxedSort],
                                                   range: A): Cvc5Term =
      funcMap.getOrElseUpdate(name, {
        val domainSorts = domain.map(ds => lowerSort(ds.sort))
        val rangeSort = lowerSort(range)
        solver.declareFun(name, domainSorts.toArray, rangeSort)
      })

    override def liftSort(sort: Cvc5Sort): Core.BoxedSort =
      val sortName = sort.toString
      if sort.isBoolean then
        Core.BoolSort().box
      else if sort.isInteger then
        Core.NumericSort().box
      else if sort.isArray then
        val domSort = liftSort(sort.getArrayIndexSort)
        val rangeSort = liftSort(sort.getArrayElementSort)
        Core.arraySort(domSort, rangeSort)
      else if sort.isUninterpretedSort then
        typeEnv.lookup(sortName).getOrElse {
          val numArgs = 0 // CVC5 doesn't expose arity directly
          Core.UnInterpretedSort(sortName, numArgs).box
        }
      else if sort.isDatatype then
        typeEnv.lookup(sortName).getOrElse {
          unexpected(s"liftSort: datatype sort $sortName not found in type environment", sort)
        }
      else
        unsupported(s"liftSort: unsupported CVC5 sort for $sortName")

    override def liftTerm(term: Cvc5Term): Core.BoxedExpr =
      // Handle boolean constants
      if term.isBooleanValue then
        return Core.mkConst(term.getBooleanValue).box()

      // Handle integer constants
      if term.isIntegerValue then
        return Core.mkConst(term.getIntegerValue.intValue()).box()

      // Handle uninterpreted sort values
      if term.isUninterpretedSortValue then
        val name = term.getUninterpretedSortValue
        val sort = liftSort(term.getSort)
        liftSort(term.getSort) match {
          case u@Core.UnInterpretedSort(_, _) => return Core.mkConst(Core.SortValue.UnInterpretedValue(name, u))
          case _ => unexpected(s"liftTerm: uninterpreted sort value $name has non-uninterpreted sort $sort", term)
        }

      // Handle const arrays
      if term.isConstArray then
        val baseValue = liftTerm(term.getConstArrayBase)
        val arraySort = liftSort(term.getSort)
        arraySort.sort match
          case arr@Core.ArraySort(_, _) =>
            baseValue.unify(arr.rangeSort) match
              case Some(unifiedBase) =>
                return Core.mkConstArray(arr.domainSort, unifiedBase)
              case None =>
                unexpected(s"liftTerm: const array base $baseValue does not match range ${arr.rangeSort}", term)
          case _ =>
            unexpected(s"liftTerm: const array has non-array sort $arraySort", term)

      // Handle general terms by kind
      val kind = term.getKind
      import io.github.cvc5.Kind

      kind match
        case Kind.CONSTANT =>
          // Variables and constants declared with mkConst
          val sort = liftSort(term.getSort)
          val name = if term.hasSymbol then term.getSymbol else term.toString
          interpEnv.lookup(name) match
            case Some(expr) => expr
            case None => Core.mkVar(name, sort).box()

        case Kind.VARIABLE =>
          // Bound variables (from quantifiers)
          val sort = liftSort(term.getSort)
          val name = if term.hasSymbol then term.getSymbol else s"var_${term.getId}"
          Core.mkVar(name, sort).box()

        case Kind.EQUAL =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: EQUAL expects 2 children, got ${children.length}", term)
          val lhs = liftTerm(children(0))
          val rhs = liftTerm(children(1))
          rhs.e.unify(lhs.sort) match
            case Some(unifiedRhs) => Core.mkEq(lhs.e, unifiedRhs).box()
            case None => unexpected(s"liftTerm: EQUAL type mismatch: $lhs vs $rhs", term)

        case Kind.ITE =>
          val children = getChildren(term)
          if children.length != 3 then
            unexpected(s"liftTerm: ITE expects 3 children, got ${children.length}", term)
          val cond = liftTerm(children(0))
          val thn = liftTerm(children(1))
          val els = liftTerm(children(2))
          (cond.unify(Core.BoolSort()), thn.unify(els.sort)).tupled match
            case Some(unifiedCond, unifiedThn) =>
              Core.mkIte(unifiedCond, unifiedThn, els.e).box()
            case None =>
              unexpected(s"liftTerm: ITE type mismatch: cond=$cond, thn=$thn, els=$els", term)

        case Kind.AND =>
          val children = getChildren(term).map(liftTerm)
          Core.unifyTerms(children.toList, Core.BoolSort()) match
            case Some(unified) => Core.mkAnd(unified).box()
            case None => unexpected(s"liftTerm: AND children type mismatch", term)

        case Kind.OR =>
          val children = getChildren(term).map(liftTerm)
          Core.unifyTerms(children.toList, Core.BoolSort()) match
            case Some(unified) => Core.mkOr(unified).box()
            case None => unexpected(s"liftTerm: OR children type mismatch", term)

        case Kind.NOT =>
          val children = getChildren(term)
          if children.length != 1 then
            unexpected(s"liftTerm: NOT expects 1 child, got ${children.length}", term)
          val child = liftTerm(children(0))
          child.unify(Core.BoolSort()) match
            case Some(unifiedChild) => Core.mkNot(unifiedChild).box()
            case None => unexpected(s"liftTerm: NOT child is not boolean: $child", term)

        case Kind.IMPLIES =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: IMPLIES expects 2 children, got ${children.length}", term)
          val premise = liftTerm(children(0))
          val conclusion = liftTerm(children(1))
          (premise.unify(Core.BoolSort()), conclusion.unify(Core.BoolSort())).tupled match
            case Some(unifiedPremise, unifiedConclusion) =>
              Core.mkImplies(unifiedPremise, unifiedConclusion).box()
            case None =>
              unexpected(s"liftTerm: IMPLIES type mismatch", term)

        case Kind.ADD =>
          val children = getChildren(term).map(liftTerm)
          Core.unifyTerms(children.toList, Core.NumericSort()) match
            case Some(unified) => Core.mkAdd(unified).box()
            case None => unexpected(s"liftTerm: ADD children type mismatch", term)

        case Kind.SUB =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: SUB expects 2 children, got ${children.length}", term)
          val lhs = liftTerm(children(0))
          val rhs = liftTerm(children(1))
          (lhs.unify(Core.NumericSort()), rhs.unify(Core.NumericSort())).tupled match
            case Some(unifiedLhs, unifiedRhs) =>
              Core.mkMinus(unifiedLhs, unifiedRhs).box()
            case None =>
              unexpected(s"liftTerm: SUB type mismatch", term)

        case Kind.MULT =>
          val children = getChildren(term).map(liftTerm)
          Core.unifyTerms(children.toList, Core.NumericSort()) match
            case Some(unified) => Core.mkMul(unified).box()
            case None => unexpected(s"liftTerm: MULT children type mismatch", term)

        case Kind.NEG =>
          val children = getChildren(term)
          if children.length != 1 then
            unexpected(s"liftTerm: NEG expects 1 child, got ${children.length}", term)
          val child = liftTerm(children(0))
          child.unify(Core.NumericSort()) match
            case Some(unifiedChild) => Core.mkNegative(unifiedChild).box()
            case None => unexpected(s"liftTerm: NEG child is not numeric: $child", term)

        case Kind.LT | Kind.LEQ | Kind.GT | Kind.GEQ =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: comparison expects 2 children, got ${children.length}", term)
          val lhs = liftTerm(children(0))
          val rhs = liftTerm(children(1))
          val op = kind match
            case Kind.LT => "<"
            case Kind.LEQ => "<="
            case Kind.GT => ">"
            case Kind.GEQ => ">="
          (lhs.unify(Core.NumericSort()), rhs.unify(Core.NumericSort())).tupled match
            case Some(unifiedLhs, unifiedRhs) =>
              Core.mkBop(op, unifiedLhs, unifiedRhs, Core.BoolSort())
            case None =>
              unexpected(s"liftTerm: comparison type mismatch", term)

        case Kind.SELECT =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: SELECT expects 2 children, got ${children.length}", term)
          val arr = liftTerm(children(0))
          val idx = liftTerm(children(1))
          arr.sort match
            case arrSort@Core.ArraySort(_, _) =>
              arr.unify(Core.ArraySort(idx.sort, arrSort.rangeSort)) match
                case Some(unifiedArr) =>
                  Core.mkSelect(unifiedArr, idx.e).box()
                case None =>
                  unexpected(s"liftTerm: SELECT index type mismatch", term)
            case _ =>
              unexpected(s"liftTerm: SELECT on non-array: ${arr.sort}", term)

        case Kind.STORE =>
          val children = getChildren(term)
          if children.length != 3 then
            unexpected(s"liftTerm: STORE expects 3 children, got ${children.length}", term)
          val arr = liftTerm(children(0))
          val idx = liftTerm(children(1))
          val value = liftTerm(children(2))
          arr.unify(Core.ArraySort(idx.sort, value.sort)) match
            case Some(unifiedArr) =>
              Core.mkStore(unifiedArr, idx.e, value.e).box()
            case None =>
              unexpected(s"liftTerm: STORE type mismatch", term)

        case Kind.FORALL | Kind.EXISTS =>
          val children = getChildren(term)
          if children.length != 2 then
            unexpected(s"liftTerm: quantifier expects 2 children, got ${children.length}", term)
          val varList = children(0)
          val body = children(1)

          if varList.getKind != Kind.VARIABLE_LIST then
            unexpected(s"liftTerm: expected VARIABLE_LIST, got ${varList.getKind}", term)

          val vars = getChildren(varList).map { v =>
            val name = if v.hasSymbol then v.getSymbol else s"var_${v.getId}"
            val sort = liftSort(v.getSort)
            (name, sort)
          }.toList

          val bodyExpr = liftTerm(body)
          bodyExpr.unify(Core.BoolSort()) match
            case Some(unifiedBody) =>
              if kind == Kind.FORALL then
                Core.mkForall(vars, unifiedBody).box()
              else
                Core.mkExists(vars, unifiedBody).box()
            case None =>
              unexpected(s"liftTerm: quantifier body is not boolean: $bodyExpr", term)

        case Kind.APPLY_UF =>
          val children = getChildren(term)
          if children.isEmpty then
            unexpected(s"liftTerm: APPLY_UF expects at least 1 child", term)

          val funcTerm = children(0)
          val args = children.tail.toList.map(liftTerm)
          val funcName = if funcTerm.hasSymbol then funcTerm.getSymbol else funcTerm.toString

          interpEnv.lookup(funcName) match
            case Some(funcExpr) =>
              // Try as uninterpreted function
              val retSort = liftSort(term.getSort)
              val domainSorts = args.toList.map(_.sort.box)
              val funSort = Core.funSort(domainSorts, retSort)
              funcExpr.unify(funSort) match {
                case Some(_) =>
                  val func = Core.mkVar(funcName, funSort)
                  val bindings = args.zipWithIndex.map { case (arg, i) =>
                    (s"arg_$i", arg)
                  }
                  Core.mkSubst("app", bindings, func).box()
                case None => unexpected(s"CVC5 function definition ${funcName} does not match ${funcExpr} in environment")
              }
            case None =>
              // Undeclared function
              val retSort = liftSort(term.getSort)
              val domainSorts = args.map(_.sort.box)
              val funSort = Core.funSort(domainSorts, retSort)
              val func = Core.mkVar(funcName, funSort)
              interpEnv.add(funcName, Core.mkVar(funcName, funSort))
              val bindings = args.zipWithIndex.map { case (arg, i) =>
                (s"arg_$i", arg)
              }
              Core.mkSubst("app", bindings, func).box()

        case Kind.APPLY_TESTER =>
          val children = getChildren(term)
          if children.length != 1 then
            unexpected(s"liftTerm: APPLY_TESTER expects 1 child, got ${children.length}", term)
          val arg = liftTerm(children(0))
          val parentSort = arg.sort
          parentSort match
            case dt: Core.DatatypeConstructorSort =>
              val testerName = if term.hasSymbol then term.getSymbol else term.toString
              val constructorName = testerName.stripPrefix("(_ is ") match
                case s if s.endsWith(")") => s.dropRight(1)
                case other => other
              val recognizer = Core.mkDatatypeRecognizer(dt, constructorName, arg.e.asInstanceOf[Core.Expr[Core.DatatypeConstructorSort]])
              recognizer.box()
            case _ =>
              unexpected(s"liftTerm: APPLY_TESTER on non-datatype argument: ${arg.sort}", term)

        case Kind.APPLY_CONSTRUCTOR =>
          val children = getChildren(term)
          val dtSort = liftSort(term.getSort)
          dtSort.sort match
            case dt: Core.DatatypeConstructorSort =>
              if children.isEmpty then
                // Nullary constructor
                val ctorTerm = term
                val ctorName = if ctorTerm.hasSymbol then ctorTerm.getSymbol else ctorTerm.toString
                dt.lookupConstructor(ctorName) match
                  case Some(ctor) =>
                    val inst = Core.InstantiatedConstructor(ctor, Nil)
                    Core.mkDatatypeAccessor(dt, inst).box()
                  case None =>
                    unexpected(s"liftTerm: constructor $ctorName not found in datatype $dt", term)
              else
                // N-ary constructor: first child is constructor, rest are arguments
                val ctorTerm = children(0)
                val ctorName = if ctorTerm.hasSymbol then ctorTerm.getSymbol else ctorTerm.toString
                val args = children.tail.map(liftTerm)
                dt.lookupConstructor(ctorName) match
                  case Some(ctor) =>
                    val inst = Core.InstantiatedConstructor(ctor, args.toList)
                    Core.mkDatatypeAccessor(dt, inst).box()
                  case None =>
                    unexpected(s"liftTerm: constructor $ctorName not found in datatype $dt", term)
            case _ =>
              unexpected(s"liftTerm: APPLY_CONSTRUCTOR on non-datatype sort: $dtSort", term)

        case _ =>
          unsupported(s"liftTerm: unsupported CVC5 kind $kind for term $term")

    private def getChildren(term: Cvc5Term): Array[Cvc5Term] =
      val numChildren = term.getNumChildren
      (0 until numChildren).map(term.getChild).toArray

    override def liftFunc(func: Cvc5Term): Core.BoxedExpr =
      val funcName = if func.hasSymbol then func.getSymbol else func.toString
      interpEnv.lookup(funcName).getOrElse {
        val sort = liftSort(func.getSort)
        Core.mkVar(funcName, sort).box()
      }

    override def lookupDecl[S <: Sort[S]](v: String, s: S): Option[LoweredVarDecl] = {
      try Some(funcMap(v)) catch case _ => None
    }

    override def initialize(logic: SmtSolver.Logic): Unit = {
      solver.setOption("produce-models", "true")
      // solver.setOption("produce-unsat-cores", "true")
      solver.setOption("produce-interpolants", "true")
      solver.setOption("incremental", "true")
      val logicName = SmtSolver.parseLogic(logic)
      solver.setLogic(logicName)
      record(s"initialize($logicName)")

      typeEnv.registerUpdateHook { (name, sort) =>
        val lowered = defineSort(sort.sort)
        s"defineSort ${name}: ${lowered.toString}"
      }

      interpEnv.registerUpdateHook { (name, expr) =>
        val (decl, _) = defineVar(name, expr.sort, expr.e)
        s"defineVar ${name}: ${decl.toString}"
      }

      typeEnv.foreach { case (_, boxedSort) => ignore(defineSort(boxedSort.sort)) }
      interpEnv.foreach { case (n, boxedExpr) => ignore(defineVar(n, boxedExpr.sort, boxedExpr.e)) }

    }

    override def add(fs: List[Core.BoxedExpr]): List[Cvc5Term] = {
      val lowered = fs.map(expr => lower(expr.e))
      lowered.foreach(solver.assertFormula)
      record(s"add(${fs.map(_.toString).mkString(",")})")
      lowered
    }

    override def addTerms(terms: List[Cvc5Term]): List[Cvc5Term] = {
      terms.foreach(solver.assertFormula)
      record(s"addTerms(${terms.map(_.toString).mkString(",")})")
      terms
    }

    override def push(): Unit = solver.push()

    override def pop(): Unit = solver.pop()

    override def reset(): Unit = {
      solver.resetAssertions()
      exprMap.clear()
      record("reset()")
    }

    override def fork(): Cvc5Solver = new Cvc5Solver(typeEnv.copy(), interpEnv.copy())

    override def getModel: Option[SmtSolver.Model[Cvc5Term, Cvc5Term]] = {
      try {
        Some(new Cvc5Model(this))
      } catch
        case t: Throwable =>
          println("CVC5 threw an error during getModel: " + t.toString)
          None
    }

    override def getUnsatCore: Option[SmtSolver.UnsatCore[Cvc5Term, Cvc5Term]] = {
      try {
        val coreTerms = solver.getUnsatCore
        Some(Cvc5UnsatCore(coreTerms.toSet, this))
      } catch {
        case _ => None
      }
    }

    override def checkSat(): SmtSolver.Result = {
      val result = solver.checkSat()
      if result.isSat then SmtSolver.Result.SAT
      else if result.isUnsat then SmtSolver.Result.UNSAT
      else SmtSolver.Result.UNKNOWN
    }
  }

  class Cvc5UnsatCore(coreTerms: Set[Cvc5Term], solver: Cvc5Solver) extends SmtSolver.UnsatCore[Cvc5Term, Cvc5Term](solver) {

    override def terms(): Set[Cvc5Term] = coreTerms

    override def formulas(): Set[Expr[BoolSort]] =
      coreTerms.map(x => solver.liftTerm(x).unify(Core.boolSort).get)
  }

  class Cvc5Model(cvc5: Cvc5Solver)
    extends SmtSolver.Model[Cvc5Term, Cvc5Term](cvc5) {

    private val solverRef = cvc5.getSolver
    private val termManager = cvc5.getTermManager

    private val constSymbols = cvc5.declaredConstants
    private val funcSymbols = cvc5.declaredFunctions

    private val constantAssignments: Map[String, (Cvc5Term, Cvc5Term)] =
      constSymbols.map { case (name, symbol) =>
        name -> (symbol, solverRef.getValue(symbol))
      }.toMap

    private val functionAssignments: Map[String, (Cvc5Term, Cvc5Term)] =
      funcSymbols.map { case (name, symbol) =>
        name -> (symbol, solverRef.getValue(symbol))
      }.toMap

    private val substitutionFrom: Array[Cvc5Term] =
      (constantAssignments.values.map(_._1) ++ functionAssignments.values.map(_._1)).toArray

    private val substitutionTo: Array[Cvc5Term] =
      (constantAssignments.values.map(_._2) ++ functionAssignments.values.map(_._2)).toArray

    private def substituteAll(term: Cvc5Term): Cvc5Term =
      if substitutionFrom.isEmpty then term
      else term.substitute(substitutionFrom, substitutionTo)

    private def mkAnd(terms: List[Cvc5Term]): Cvc5Term =
      terms match
        case Nil => termManager.mkTrue()
        case head :: Nil => head
        case head :: tail =>
          tail.foldLeft(head) { (acc, next) =>
            termManager.mkTerm(Kind.AND, acc, next)
          }

    private def equalitiesFor(assignments: Iterable[(Cvc5Term, Cvc5Term)]): List[Cvc5Term] =
      assignments.toList.map { case (symbol, value) =>
        termManager.mkTerm(Kind.EQUAL, symbol, value)
      }

    private def equalityForName(name: String, sort: Core.BoxedSort): Option[Cvc5Term] = {
      constantAssignments.get(name)
        .orElse(functionAssignments.get(name))
        .map { case (symbol, value) =>
          termManager.mkTerm(Kind.EQUAL, symbol, value)
        }
    }

    override def formula(): Core.Expr[Core.BoolSort] = {
      val boxed = cvc5.liftTerm(asTerm())
      boxed.unify(Core.BoolSort()) match
        case Some(expr) => expr
        case None => unexpected("CVC5 model formula is not boolean")
    }

    override def formula(vocab: Set[(String, Core.BoxedSort)]): Core.Expr[Core.BoolSort] = {
      val boxed = cvc5.liftTerm(asTerm(vocab))
      boxed.unify(Core.BoolSort()) match
        case Some(expr) => expr
        case None => unexpected("CVC5 model formula(vocab) is not boolean")
    }

    override def valueOf[S <: Core.Sort[S]](s: String, sort: S): Option[Core.Expr[S]] =
      constantAssignments.get(s).flatMap { case (_, valueTerm) =>
        cvc5.liftTerm(valueTerm).unify(sort)
      }.orElse {
        functionAssignments.get(s).flatMap { case (_, valueTerm) =>
          cvc5.liftTerm(valueTerm).unify(sort)
        }
      }

    override def vocabulary(): (List[Core.BoxedSort], List[String]) = {
      val names = constantAssignments.keys.toList
      val sorts = constantAssignments.values.toList.map { case (symbol, _) =>
        cvc5.liftSort(symbol.getSort)
      }
      (sorts, names)
    }

    override def evaluate[S <: Core.Sort[S]](e: Core.Expr[S]): Core.Expr[S] = {
      val lowered = cvc5.lower(e)
      val substituted = substituteAll(lowered)
      cvc5.liftTerm(substituted).unify(e.sort) match {
        case Some(unified) => unified
        case None => unexpected(s"cvc5 model evaluation: got expression ${substituted} but expected sort ${e.sort} of ${e}")
      }
    }

    override def asNegatedTerm(): Cvc5Term =
      termManager.mkTerm(Kind.NOT, asTerm())

    override def asNegatedTerm(vocab: Set[(String, Core.BoxedSort)]): Cvc5Term =
      termManager.mkTerm(Kind.NOT, asTerm(vocab))

    override def asTerm(): Cvc5Term =
      mkAnd(
        equalitiesFor(constantAssignments.values) ++
          equalitiesFor(functionAssignments.values)
      )

    override def asTerm(vocabulary: Set[(String, Core.BoxedSort)]): Cvc5Term =
      mkAnd(
        vocabulary.toList.flatMap { case (name, sort) =>
          equalityForName(name, sort)
        }
      )

    override def toString: String = {
      val assignments = constantAssignments.keys.toList.sorted.map { name =>
        val value = constantAssignments(name)._2
        s"$name = ${value.toString}"
      }.mkString(", ")
      s"CVC5 Model {$assignments}"
    }

    override def apply(arg: String, sort: Core.BoxedSort): Option[Core.BoxedExpr] = {
      constantAssignments.get(arg)
        .orElse(functionAssignments.get(arg))
        .flatMap { case (_, valueTerm) =>
          val boxed = cvc5.liftTerm(valueTerm)
          boxed.unify(sort.sort).map(_.box())
        }
    }
  }
}
