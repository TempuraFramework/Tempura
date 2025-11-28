package org.abstractpredicates.smt

import com.microsoft.z3
import com.microsoft.z3.{ArraySort, Expr, FuncDecl, FuncInterp, Solver, Sort, Status}
import com.microsoft.z3.enumerations.{Z3_decl_kind, Z3_lbool, Z3_sort_kind}
import org.abstractpredicates.expression.{Core, LetRemover, Visitor}
import org.abstractpredicates.expression.Syntax.*
import org.abstractpredicates.helpers.Utils.*
import cats.syntax.all.*
import cats.Traverse
import cats.implicits.*
import com.microsoft.z3.FuncDecl.Parameter
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.smt.SmtSolver.Result
import org.abstractpredicates.helpers.Utils.*

import scala.collection.mutable
import scala.collection.mutable.ArrayDeque as Stack


object Z3Solver {

  class Z3Solver(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)
    extends SmtSolver.Solver[z3.Expr[z3.Sort], z3.FuncDecl[z3.Sort]](typeEnv, interpEnv) {


    private def typeEnvUpdateHook(name: String, sort: Core.BoxedSort) =
      name + " : " + (this.defineSort(sort)).toString

    private def interpEnvUpdateHook(name: String, expr: Core.BoxedExpr) =
      name + " : " + (this.defineVar(name, expr.sort, expr.e)).toString

    override type LoweredSort = z3.Sort

    private var history: List[String] = List()

    private def appendHistory(s: String): Unit = history = s :: history

    override def getHistory: List[String] = history

    // Z3-specific objects
    private val context = new z3.Context()
    private val solver: Solver = context.mkSolver()
    val version: String = com.microsoft.z3.Version.getFullVersion


    // Caching
    private val exprMap: scala.collection.mutable.Map[Core.BoxedExpr, LoweredTerm] = scala.collection.mutable.Map()
    private val sortMap: scala.collection.mutable.Map[Core.BoxedSort, LoweredSort] = scala.collection.mutable.Map()
    // In our IR, a function symbol is either a Macro[t] or a Var[FunSort[t]] instance.
    // So technically, the `funcMap`` instance below could map from a BoxedExpr to a LoweredFunc.
    // We opted to simply map from the String-representation to a LoweredFunc instead, because in fact
    // we can define an uninterpreted function at any arbitrary point-in-time, thus it is not always safe
    // to map from a function symbol's AST representation (as it can change between a Macro[t] and a Var[FunSort[t]]).
    private val funcMap: scala.collection.mutable.Map[String, LoweredVarDecl] = scala.collection.mutable.Map()

    // Additionally, defined function symbols might come with axioms.
    // In Z3, there is no way to define an uninterpreted symbol besides constraining its output as an additional axiom.
    // These axioms are eagerly added to the solver, but we save them in a map as well.
    private val axiomMap: scala.collection.mutable.Map[String, LoweredTerm] = scala.collection.mutable.Map()

    // Look up a Z3 sort from a Core sort, return None if given sort is not lowered before.
    private def toZ3Sort(s: BoxedSort): Option[z3.Sort] = sortMap.get(s)

    // Look up a Z3 FunDecl from its name, returns none if given name has not been declared/defined before.
    private def toZ3Func(name: String): Option[LoweredVarDecl] = funcMap.get(name)

    // Look up a Z3 expression from a corresponding expression, returns none if given expression has not been
    // lowered before. This amounts to performing hash-consing at the solver interface-level.
    private def toZ3Expr(e: BoxedExpr): Option[LoweredTerm] = exprMap.get(e)

    // Lower a sort into a Z3 sort, returns the previously cached lowering result if the given
    // sort has been lowered before.
    private def newZ3Sort[A <: Core.Sort[A]](s: A, resolver: A => z3.Sort): Sort = {
      toZ3Sort(s) match {
        case Some(s) => s
        case None =>
          val z3sort = resolver(s)
          sortMap.update(s, z3sort)
          z3sort
      }
    }

    private def newZ3Func(name: String, domainSorts: List[z3.Sort], rangeSort: z3.Sort): LoweredVarDecl = {
      toZ3Func(name) match {
        case Some(f) => f
        case None =>
          val fd = context.mkFuncDecl(name, domainSorts.toArray, rangeSort)
          funcMap.update(name, fd)
          fd
      }
    }

    // TODO: move this into the initialize() method; but this requires refactoring users of this API.
    ////////////////////// Initialization Code //////////////////////
    // register update hooks so that all subsequent calls to typeEnv/interpEnv auto-translates
    // into Z3 solver calls
    typeEnv.registerUpdateHook(typeEnvUpdateHook)
    interpEnv.registerUpdateHook(interpEnvUpdateHook)

    // turn existing entries inside typeEnv/interpEnv into Z3 solver calls
    typeEnv.foreach(t => ignore(this.defineSort(t._2)))
    interpEnv.foreach(t => ignore(this.defineVar(t._1, t._2.sort, t._2.e)))
    /////////////////////////////////////////////////////////////////

    def getContext: z3.Context = context

    def getSolver: z3.Solver = solver

    private def z3MkArraySelect(a: z3.Expr[ArraySort[z3.Sort, z3.Sort]], args: Array[z3.Expr[?]]): LoweredTerm = {
      //public
      //final <R extends Sort>Expr[R] mkSelect(a: Expr[ArraySort[Sort, R]], args: Array[Expr[_]])
      context.mkSelect(a, args)
    }

    private def z3MkArrayStore(a: z3.Expr[ArraySort[z3.Sort, z3.Sort]], idx: z3.Expr[z3.Sort], v: z3.Expr[z3.Sort]): LoweredTerm = {
      context.mkStore(a, idx, v).asInstanceOf[LoweredTerm]
    }


    private def declareFiniteUniverseSort(s: Core.FiniteUniverseSort): Sort = {
      newZ3Sort(s, s => context.mkEnumSort(s.sortName, mkEnumNames(s.sortName, s.card) *))
    }

    // XXX: Z3's Java API requires a <R> generic parameter that appears unbounded for datatype constructors.
    // So we need to pass an <Any> in here.
    //     public final <R> Constructor<R> mkConstructor(String name, String recognizer,
    //            String[] fieldNames, Sort[] sorts, int[] sortRefs)
    // Makes a multi-arity constructor (with argument sorts provided)
    private def mkConstructor[R](c: Core.Constructor): z3.Constructor[R] = {
      val argSortsT = c.args.map(x => lowerSort(x._2))
      context.mkConstructor[R](c.name, getRecognizerName(c), c.args.map(x => x._1).toArray, argSortsT.toArray, null)
    }

    // Makes a 0-arity constructor (that is effectively an enum)
    private def mkConstructor[R](constrName: String): z3.Constructor[R] = {
      context.mkConstructor[R](constrName, getRecognizerName(constrName), Array[String](), Array[z3.Sort](), null)
    }

    private def declareDatatypeConstructorSort(s: Core.DatatypeConstructorSort): LoweredSort = {
      val consT = s.constructors.map(x => mkConstructor[Any](x))
      newZ3Sort(s, s => context.mkDatatypeSort[Any](s.sortName, consT.toArray))
    }

    private def datatypeLookup(name: String, z3sort: z3.DatatypeSort[?]): Option[FuncDecl[z3.Sort]] = {
      val constructors = z3sort.getConstructors
      val ans = constructors.toList.find(_.getName.toString == name)
      ans match {
        case Some(f) => Some(f.asInstanceOf[FuncDecl[z3.Sort]])
        case None => None
      }
    }

    def getVersion: String = this.version

    override def fork(): Z3Solver = {
      val newTypeEnv = getTypeEnv.copy()
      val newInterpEnv = getInterp.copy()
      val newSolver = new Z3Solver(newTypeEnv, newInterpEnv)
      newSolver
    }

    override def lowerSort[A <: Core.Sort[A]](s: A): LoweredSort = {
      toZ3Sort(s.box) match {
        case Some(sort) => sort
        case None =>
          s match {
            case Core.NumericSort() => context.getIntSort
            case Core.BoolSort() => context.getBoolSort
            case Core.ArraySort(sortD, sortR) =>
              val dom = lowerSort(sortD)
              val range = lowerSort(sortR)
              // cache the result
              sortMap.update(s, context.mkArraySort(dom, range))
              context.mkArraySort(dom, range)
            case _ => unexpected(s"custom sort ${s.toString} is undeclared in the environment", s)
          }
      }
    }

    override def defineSort[A <: Core.Sort[A]](s: A): LoweredSort = {
      appendHistory(s"defineSort(${s.toString})")
      toZ3Sort(s.box) match {
        case Some(sort) => sort
        case None =>
          s match {
            case _: Core.NumericSort => context.getIntSort
            case _: Core.BoolSort => context.getBoolSort
            case Core.ArraySort(_, _) => lowerSort(s)
            case x: Core.UnInterpretedSort =>
              // create new sort in Z3
              println(s"creating new z3 sort ${x} in Z3...")
              val z3sort = context.mkUninterpretedSort(x.sortName)
              // update cached map
              println(s"updating sortMap with ${s} = ${z3sort}")
              sortMap.update(s, z3sort)
              println(s"sortMap: ${sortMap.toString}")
              assert(sortMap(s) == z3sort)
              z3sort
            case x: Core.AliasSort[_] =>
              // this is a little trickier.
              // an alias sort is a concrete sort we get after we accumulated enough parameters
              // for a parametric (higher-order) sort, e.g. (s Int Int) for (declare-sort s 2).
              // So we need a special name for such a sort, and translate it into a sort-declaration
              // of the underlying sort applied by it.
              val z3sort = context.mkUninterpretedSort(x.sortName)
              z3sort
            case s: Core.FiniteUniverseSort =>
              declareFiniteUniverseSort(s)
            case s: Core.DatatypeConstructorSort =>
              declareDatatypeConstructorSort(s)
            case Core.FunSort(_, _) =>
              unexpected("cannot translate function sorts in Z3", s)
          }
      }
    }


    override def lowerValue[S <: Core.Sort[S]](sortValue: Core.SortValue[S]): LoweredTerm = {
      sortValue match {
        case Core.SortValue.BoolValue(b) => context.mkBool(b).asInstanceOf[LoweredTerm]
        case Core.SortValue.NumericValue(n) => context.mkInt(n).asInstanceOf[LoweredTerm]
        case Core.SortValue.UnInterpretedValue(name, sort) =>
          val s = lowerSort(sort)
          context.mkConst(name, s)
        case Core.SortValue.ArrayValue(default, sort) =>
          val dSort = lowerSort(sort.domainSort)
          val defaultT = lower(default)
          context.mkConstArray(dSort, defaultT).asInstanceOf[LoweredTerm]
        case Core.SortValue.FiniteUniverseValue(index, finiteUniverseSort) =>
          val sortT = lowerSort(finiteUniverseSort)
          sortT.asInstanceOf[z3.EnumSort[z3.Sort]].getConst(index).asInstanceOf[LoweredTerm]
        case Core.SortValue.DatatypeValue(constructorName, sort) =>
          val sortT = lowerSort(sort)
          datatypeLookup(constructorName.getName, sortT.asInstanceOf[z3.DatatypeSort[?]]) match {
            case Some(cons) =>
              cons.asInstanceOf[LoweredTerm]
            case None =>
              unexpected("constructor not found", sortValue)
          }
        case Core.SortValue.AliasSortValue(name, sort) =>
          val z3Sort = lowerSort(sort)
          context.mkConst(name, z3Sort)
      }
    }

    override def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): LoweredTerm = {
      lower(Map[String, LoweredVarDecl]())(expr)
    }

    // boundVars denote bound variables created by
    // Forall/Exists/etc that get passed in. The de Bruijn-indexed variables
    // are not among this list, but are treated as variables with special names
    // storing their index.
    private def lower[S <: Core.Sort[S]](boundVars: Map[String, LoweredVarDecl])(expr: Core.Expr[S]): LoweredTerm =
      expr match {
        case Var(n, sort) =>
          val z3Sort = lowerSort(sort)
          testBoundVarName(n) match { // for lambda bound variables
            case Some(idx) =>
              context.mkBound(idx, z3Sort)
            case None => (funcMap.get(n), boundVars.get(n)) match { // for others and array bound variables
              case (_, Some(funDecl)) => // bound variables take precedence.
                funDecl.apply()
              case (Some(funDecl), _) =>
                funDecl.apply()
              case (None, None) =>
                unexpected(s"variable ${n} previously undeclared", expr)
            }
          }
        case Const(sv) => lowerValue(sv)
        case ArraySelect(arrExpr, arrIndex) =>
          val arr = lower(boundVars)(arrExpr)
          val index = lower(boundVars)(arrIndex)
          z3MkArraySelect(arr.asInstanceOf[z3.Expr[ArraySort[z3.Sort, z3.Sort]]], Array(index))
        case ArrayStore(arrExpr, arrIndex, arrVal) =>
          val arr = lower(boundVars)(arrExpr)
          val index = lower(boundVars)(arrIndex)
          val v = lower(boundVars)(arrVal)
          z3MkArrayStore(arr.asInstanceOf[z3.Expr[z3.ArraySort[z3.Sort, z3.Sort]]],
            index,
            v)
        case Bop("at-most", number, Lop("at-most", args, _, _), _) =>
          val i = number match {
            case Const(Core.SortValue.NumericValue(n)) => n
            case _ => failwith("")
          }
          val argsT = args.map(lower(boundVars))
          context.mkAtMost(argsT.map(x => x.asInstanceOf[z3.Expr[z3.BoolSort]]).toArray, i).asInstanceOf[LoweredTerm]
        case Bop("at-least", number, Lop("at-least", args, _, _), _) =>
          val i = number match {
            case Const(Core.SortValue.NumericValue(n)) => n
            case _ => failwith("")
          }
          val argsT = args.map(lower(boundVars))
          context.mkAtLeast(argsT.map(x => x.asInstanceOf[z3.Expr[z3.BoolSort]]).toArray, i).asInstanceOf[LoweredTerm]
        case Bop(numericComp, lhs, rhs, _) if numericComp == ">" || numericComp == "<" || numericComp == ">=" || numericComp == "<=" =>
          val lhsT = lower(boundVars)(lhs)
          val rhsT = lower(boundVars)(rhs)

          (numericComp match {
            case ">" => context.mkGt(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]])
            case "<" => context.mkLt(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]])
            case ">=" => context.mkGe(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]])
            case "<=" => context.mkLe(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]])
          }).asInstanceOf[LoweredTerm]

        case Lop(numericOp, args, _, _) if numericOp == "+" || numericOp == "*" =>
          val argsT = args.map(lower(boundVars))
          numericOp match {
            case "+" => context.mkAdd(argsT.map(x => x.asInstanceOf[z3.Expr[z3.ArithSort]]) *).asInstanceOf[LoweredTerm]
            case "*" => context.mkMul(argsT.map(x => x.asInstanceOf[z3.Expr[z3.ArithSort]]) *).asInstanceOf[LoweredTerm]
          }
        case Bop(numericOp, lhs, rhs, _) if numericOp == "-" || numericOp == "/" =>
          val lhsT = lower(boundVars)(lhs)
          val rhsT = lower(boundVars)(rhs)
          numericOp match {
            case "-" => context.mkSub(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]]).asInstanceOf[LoweredTerm]
            case "/" => context.mkDiv(lhsT.asInstanceOf[z3.Expr[z3.ArithSort]], rhsT.asInstanceOf[z3.Expr[z3.ArithSort]]).asInstanceOf[LoweredTerm]
          }
        case Uop("-", subExpr, Core.NumericSort()) =>
          val subExprT = lower(boundVars)(subExpr)
          context.mkUnaryMinus(subExprT.asInstanceOf[z3.Expr[z3.ArithSort]]).asInstanceOf[LoweredTerm]
        case Top("=>", premise, thenBranch, elseBranch, _) =>
          val premiseT = lower(boundVars)(premise)
          val thenBranchT = lower(boundVars)(thenBranch)
          val elseBranchT = lower(boundVars)(elseBranch)
          context.mkITE(premiseT.asInstanceOf[z3.BoolExpr], thenBranchT, elseBranchT)
        case Bop("=>", premise, implied, _) =>
          val premiseT = lower(boundVars)(premise)
          val impliedT = lower(boundVars)(implied)
          context.mkImplies(
            premiseT.asInstanceOf[z3.BoolExpr],
            impliedT.asInstanceOf[z3.BoolExpr]).asInstanceOf[LoweredTerm]
        case Bop("=", lhs, rhs, _) =>
          val lhsT = lower(boundVars)(lhs)
          val rhsT = lower(boundVars)(rhs)
          context.mkEq(lhsT, rhsT).asInstanceOf[LoweredTerm]
        case Uop("not", subExpr, _) =>
          val e = lower(boundVars)(subExpr)
          context.mkNot(e.asInstanceOf[z3.Expr[z3.BoolSort]]).asInstanceOf[LoweredTerm]
        case Lop("and", args, _, _) =>
          val argsT = args.map(lower(boundVars))
          context.mkAnd(argsT.map(x => x.asInstanceOf[z3.Expr[z3.BoolSort]]) *).asInstanceOf[LoweredTerm]
        case Lop("or", args, _, _) =>
          val argsT = args.map(lower(boundVars))
          context.mkOr(argsT.map(x => x.asInstanceOf[z3.Expr[z3.BoolSort]]) *).asInstanceOf[LoweredTerm]
        // Translation of (as-array (lambda ...))
        case Uop("as-array", lambdaExpr, _) =>
          unsupported("unimplemented as-array")
        // XXX: Z3's Java API supports two modes of reasoning about bound variables.
        // The first mode involves manually tracking de-Bruijn indices using mkBound(-) and then
        // calling mkForall/mkExists/... with variables specified as a Symbol[] array, except
        // each Symbol instance inside the Symbol[] array must be a _bound variable_ acquired from mkBound(-).
        //
        // The second mode (which is the mode used) involves passing bound vars as a list Expr<?>[] of constants,
        // each created using mkConst. This is the approach we'll take --- the list of constants are dynamically
        // instantiated using mkConst(-) in-place.
        case Forall(sortedArgs, body) =>
          val newBoundVars = scala.collection.mutable.Map.from(boundVars)
          val argTerms = sortedArgs.map(x =>
            val lSort = lowerSort(x._2)
            val boundVar = context.mkConst(x._1, lSort)
            newBoundVars.update(x._1, boundVar.getFuncDecl)
            boundVar
          )
          val termBody = lower(Map.from(newBoundVars))(body)
          context.mkForall(argTerms.toArray, termBody.asInstanceOf[z3.Expr[z3.BoolSort]], 1, null, null, null, null).asInstanceOf[LoweredTerm]
        case Exists(sortedArgs, body) =>
          val newBoundVars = scala.collection.mutable.Map.from(boundVars)
          val argTerms = sortedArgs.map(x =>
            val lSort = lowerSort(x._2)
            val boundVar = context.mkConst(x._1, lSort)
            newBoundVars.update(x._1, boundVar.getFuncDecl)
            boundVar
          )
          val termBody = lower(Map.from(newBoundVars))(body)
          context.mkExists(argTerms.toArray, termBody.asInstanceOf[z3.Expr[z3.BoolSort]], 1, null, null, null, null).asInstanceOf[LoweredTerm]
        // Z3 does not support let-expressions, so we need to eliminate them before passing
        // them to the SMT solver.
        case Substitute("let", _, Macro("letBody", sortedArgs, _)) =>
          val typeEnv: Core.TypeEnv = Core.Env().addFromList(sortedArgs)
          val elimExpr = (new LetRemover()).visit(Core.emptyInterpEnv)(expr)
          val newBoundVars = scala.collection.mutable.Map.from(boundVars)
          sortedArgs.foreach(x =>
            val z3sort = lowerSort(x._2)
            newBoundVars.update(x._1, context.mkFuncDecl(x._1, Array[z3.Sort](), z3sort))
          )
          lower(elimExpr)

        // We cannot handle a macro in standalone fashion. It needs to
        // be wrapped inside the body of a Substitute expression. There,
        // we case-match on the body to handle the macro. So the following case
        // should never happen.
        case Macro(name, _, _) => unexpected(s"cannot treat a function symbol ${name} as an expression", expr)
        // Handling of Substitute expressions. Note that we need to pattern-match
        // on its body sub-expression to handle macros or uninterpreted functions.
        case Substitute("app", bindings, bodyExpr) =>
          val bindingsEnv = bindings.toEnv
          val sort = bodyExpr.sort
          // There are two types of bodies to a substitute expression.
          // Either a Macro or an uninterpreted function showing up as a Var node.
          bodyExpr match {
            case Macro(name, args, expr) =>
              // First perform lowering of arguments.
              val rangeSort = lowerSort(expr.sort.box)
              val domainSorts = args.map(x => lowerSort(x._2))
              toZ3Func(name) match { // , domainSorts, rangeSort)
                case Some(f) =>
                  args.map(x => x._1).traverse(x => bindingsEnv(x)) match {
                    case Some(boundArgs) =>
                      val boundArgsT = boundArgs.map(x => lower(boundVars)(x.e))
                      context.mkApp(f, boundArgsT *)
                    case None =>
                      unexpected("Function is only partially applied: arguments missing", expr)
                  }
                case None =>
                  unexpected(s"function ${name} not declared/defined in Z3 environment", expr)
              }
            case Var(name, sortR) =>
              if sortR != sort then unexpected("sort mismatch", expr)
              else {
                toZ3Func(name) match {
                  case Some(f) =>
                    val boundArgsT = bindings.map(x => lower(boundVars)(x._2.e))
                    context.mkApp(f, boundArgsT *)
                  case None => unexpected(s"trying to apply an undeclared, uninterpreted function in Z3: ${name}", expr)
                }
              }
            case _ =>
              unexpected("cannot apply a non-function symbol", expr)
          }
        case _ => unsupported(s"lower: unsupported expression: ${expr}")
      }


    private def parseZ3Constructor(f: LoweredVarDecl, consArgs: List[LoweredTerm], dtc: Core.Constructor): Option[Core.InstantiatedConstructor] = {
      val consName = f.getName.toString
      val args = consArgs.map(liftTerm)
      if args.size != dtc.args.size then None else {
        Some(Core.InstantiatedConstructor(dtc, args))
      }
    }


    // Reference for Z3 OPCODEs: https://z3prover.github.io/api/html/group__capi.html#ga1fe4399e5468621e2a799a680c6667cd
    // Reference 2: https://pub.dev/documentation/z3/latest/z3_ffi/Z3_decl_kind-class.html
    // attempt to parse back an expression at the IR-level from
    // a term inside the model. The features this supports is limited at best, and
    // is experimental when it comes to parsing array-sorted expressions.
    // In particular,
    //
    // Some more documentation about de Bruijn indexing in Z3:
    // From line 4858 of z3/src/api/z3_api.h:
    //        \brief Create a lambda expression. It takes an expression \c body that contains bound variables
    //       of the same sorts as the sorts listed in the array \c sorts. The bound variables are de-Bruijn indices created
    //       using #Z3_mk_bound. The array \c decl_names contains the names that the quantified formula uses for the
    //       bound variables. Z3 applies the convention that the last element in the \c decl_names and \c sorts array
    //       refers to the variable with index 0, the second to last element of \c decl_names and \c sorts refers
    //       to the variable with index 1, etc.
    //       The sort of the resulting expression is \c (Array sorts range) where \c range is the sort of \c body.
    //       For example, if the lambda binds two variables of sort \c Int and \c Bool, and the \c body has sort \c Real,
    //       the sort of the expression is \c (Array Int Bool Real).
    //
    // As an example, consider the following nested expression:
    //
    //     val nested =
    //      Core.mkForall(
    //        List(("m", Core.NumericSort()), ("n", Core.NumericSort()), ("p", Core.boolSort)),
    //        Core.mkExists(
    //          List(("x", Core.numericSort), ("y", Core.boolSort)),
    //          Core.mkForall(
    //            List(("a", Core.boolSort), ("b", Core.boolSort)),
    //            Core.mkAnd(List(
    //              Core.mkEq(Core.mkVar("a", Core.boolSort), Core.mkConst(true)),
    //              Core.mkEq(Core.mkVar("b", Core.boolSort), Core.mkConst(true)),
    //              Core.mkEq(Core.mkVar("x", Core.numericSort), Core.mkConst(1)),
    //              Core.mkEq(Core.mkVar("y", Core.boolSort), Core.mkConst(true)),
    //              Core.mkEq(Core.mkVar("m", Core.NumericSort()), Core.mkConst(1)),
    //              Core.mkEq(Core.mkVar("n", Core.NumericSort()), Core.mkConst(2)),
    //              Core.mkEq(Core.mkVar("p", Core.boolSort), Core.mkConst(true))
    //            ))
    //          )
    //        )
    //      )
    //
    // If we print out the corresponding Z3 AST layer-by-layer, we get:
    // getBoundVarNames for outermost forall : List(m, n, p)
    //  body for outermost forall : (exists ((x Int) (y Bool))
    //  (forall ((a Bool) (b Bool))
    //    (and (= a true)
    //         (= b true)
    //         (= x 1)
    //         (= y true)
    //         (= (:var 6) 1)
    //         (= (:var 5) 2)
    //         (= (:var 4) true))))
    // getBoundVarNames for middle exists: List(x, y)
    //  body for middle exists: (exists ((x Int) (y Bool))
    //  (forall ((a Bool) (b Bool))
    //    (and (= a true)
    //         (= b true)
    //         (= x 1)
    //         (= y true)
    //         (= (:var 6) 1)
    //         (= (:var 5) 2)
    //         (= (:var 4) true))))
    // getBoundVarNames for inner-most forall: List(a, b)
    //  body for inner-most forall: (and (= (:var 1) true)
    //     (= (:var 0) true)
    //     (= (:var 3) 1)
    //     (= (:var 2) true)
    //     (= (:var 6) 1)
    //     (= (:var 5) 2)
    //     (= (:var 4) true))

    // Helper visitor method that recurses on sub-expressions of a Z3 expression
    // and determines the overall de-Bruijn number.
    private def deBruijnDepth(expr: z3.Expr[?]): Int = {
      expr match {
        case q: z3.Quantifier =>
          q.getNumBound + deBruijnDepth(q.getBody)
        case _ if expr.isVar =>
          0
        case _ if !expr.isVar =>
          val subExprs = expr.getArgs.toList
          subExprs.map(x => deBruijnDepth(x)).max
      }
    }

    private val deBruijnStack = Stack[String]()

    override def liftTerm(expr: LoweredTerm): BoxedExpr = {
      expr match {
        // Quantifier expressions must precede bool expressions, because Quantifier <: BoolExpr
        case quantifiedExpr: z3.Quantifier =>
          val isUniversal = quantifiedExpr.isUniversal
          // argNames: highest de-Bruijn index is last, lowest is first.
          val argNames = quantifiedExpr.getBoundVariableNames.toList.map(x => x.toString)

          deBruijnStack.appendAll(argNames)

          val argSorts = quantifiedExpr.getBoundVariableSorts.toList
          val body = quantifiedExpr.getBody

          val expr = liftTerm(body.asInstanceOf[LoweredTerm])
          val argSortsT = argSorts.map(liftSort)

          deBruijnStack.remove(0, argNames.size)

          expr.unify(Core.BoolSort()) match {
            case Some(boolBodyExpr) =>
              if isUniversal then {
                Core.mkForall(argNames.zip(argSortsT), boolBodyExpr)
              } else {
                assert(quantifiedExpr.isExistential)
                Core.mkExists(argNames.zip(argSortsT), boolBodyExpr)
              }
            case None =>
              unexpected("unification failed: quantifier body is not a boolean expression", body.asInstanceOf[LoweredTerm])
          }

        // lambda expressions from D->R have type ArraySort[D, R]
        case lambdaExpr: z3.Lambda[r] =>
          val argNames = lambdaExpr.getBoundVariableNames.toList.map(x => x.toString)

          deBruijnStack.appendAll(argNames)

          val argSorts = lambdaExpr.getBoundVariableSorts.toList
          val body = lambdaExpr.getBody.asInstanceOf[LoweredTerm]
          val retSort = body.getSort
          val overallSort = lambdaExpr.getSort

          val bodyT = liftTerm(body)
          val argSortsT = argSorts.map(liftSort)
          val retSortT = liftSort(retSort)
          val overallSortT = liftSort(overallSort)

          deBruijnStack.remove(0, argNames.size)

          bodyT.unify(retSortT) match {
            case Some(unifiedBody) =>
              val macroExpr = Core.mkMacro(getUniqueName("lambda"), argNames.zip(argSortsT), unifiedBody)
              overallSortT.sort match {
                case Core.ArraySort(domSort, rangeSort) =>
                  retSortT.unify(rangeSort) match {
                    case Some(unifiedRetSort) =>
                      Core.mkAsArray(macroExpr, Core.ArraySort(domSort, unifiedRetSort))
                    case None =>
                      unexpected(s"liftTerm: lambda term's array sort ${overallSortT} does not agree with range ${retSort}")
                  }
                case _ => unexpected(s"liftTerm: lambda term's array sort is not an array sort: ${overallSortT}")
              }
            case None =>
              unexpected(s"liftTerm: failed to unify lambda body ${bodyT} with return sort ${retSortT}")
          }
        case _ if expr.isTrue => Core.mkTrue
        case _ if expr.isFalse => Core.mkFalse
        // XXX: variables and constants are both Constants to Z3, so we distinguish them in `case _`.
        // case handling variables as terms, notice Const in Z3 = Vars in our framework
        // case _ if expr.isConst =>
        //   val sort = liftSort(expr.getFuncDecl.getRange)
        //  Core.mkVar(expr.getFuncDecl.getName.toString, sort)
        case _ if expr.isNumeral && expr.isInstanceOf[z3.IntNum] =>
          Core.mkConst(expr.asInstanceOf[z3.IntNum].getInt)
        case _ =>
          // handle miscellaneous things.
          // XXX: First, we need to handle z3's bound variables inside Lambdas.
          // These don't contain FuncDecl objects, so querying their decl kind
          // would result in a z3 exception.
          if expr.isVar then {
            val boundVarIdx = expr.getIndex
            val sort = liftSort(expr.getSort)
            // deBruijnStack(i) is the i-th indexed variabl ename.
            assert(deBruijnStack.size > boundVarIdx)
            val varName = deBruijnStack(boundVarIdx)
            Core.mkVar(varName, sort)
          } else {
            // Now we can safely handle the rest.
            val decl = expr.getFuncDecl
            val declKind = decl.getDeclKind
            val domainSorts = decl.getDomain.toList.map(liftSort)
            val rangeSort = liftSort(decl.getRange)

            def decodeDeclByKind(): Core.BoxedExpr = {
              declKind match {
                case Z3_decl_kind.Z3_OP_TRUE =>
                  Const(Core.SortValue.BoolValue(true))
                case Z3_decl_kind.Z3_OP_FALSE =>
                  Const(Core.SortValue.BoolValue(false))
                case Z3_decl_kind.Z3_OP_AND =>
                  val terms = expr.getArgs.toList.map(x => liftTerm(x.asInstanceOf[LoweredTerm]))
                  Core.unifyTerms(terms, Core.BoolSort()) match {
                    case Some(unifiedTerms) => Core.mkAnd(unifiedTerms)
                    case None =>
                      unexpected(s"unification of AND terms failed: ${terms.map(x => x.toString).mkString(",")}", expr)
                  }

                case Z3_decl_kind.Z3_OP_OR =>
                  val rawTerms = expr.getArgs.toList.map(x => liftTerm(x.asInstanceOf[LoweredTerm]))
                  Core.unifyTerms(rawTerms, Core.BoolSort()) match {
                    case Some(terms) => Core.mkOr(terms)
                    case None => unexpected("unification failed", expr)
                  }
                case Z3_decl_kind.Z3_OP_NOT =>
                  val term = liftTerm(expr.getArgs()(0).asInstanceOf[LoweredTerm])
                  term.unify(Core.BoolSort()) match {
                    case Some(unifiedTerm) => Core.mkNot(unifiedTerm)
                    case None => unexpected("unification failed", expr)
                  }
                case Z3_decl_kind.Z3_OP_ITE =>
                  val args = expr.getArgs
                  val cond = args(0).asInstanceOf[LoweredTerm]
                  val thenBranch = args(1).asInstanceOf[LoweredTerm]
                  val elseBranch = args(2).asInstanceOf[LoweredTerm]
                  val condR = liftTerm(cond)
                  val thenR = liftTerm(thenBranch)
                  val elseR = liftTerm(elseBranch)
                  (condR.unify(Core.BoolSort()), thenR.unify(elseR.sort)).tupled match {
                    case Some(unifiedCond, unifiedThen) =>
                      Core.mkIte(unifiedCond, unifiedThen, elseR)
                    case None =>
                      unexpected(s"unification failed for ITE terms ${condR} and ${thenR}", expr)
                  }
                case Z3_decl_kind.Z3_OP_IMPLIES =>
                  val args = expr.getArgs
                  val premise = liftTerm(args(0).asInstanceOf[LoweredTerm])
                  val conclusion = liftTerm(args(1).asInstanceOf[LoweredTerm])
                  (premise.unify(Core.BoolSort()), conclusion.unify(Core.BoolSort())).tupled match {
                    case Some(unifiedPremise, unifiedConcl) =>
                      Core.mkImplies(unifiedPremise, unifiedConcl)
                    case None =>
                      unexpected(s"unification failed for implication: ${premise} => ${conclusion}", expr)
                  }
                case Z3_decl_kind.Z3_OP_EQ =>
                  val args = expr.getArgs
                  val lhs = liftTerm(args(0).asInstanceOf[LoweredTerm])
                  val rhs = liftTerm(args(1).asInstanceOf[LoweredTerm])
                  rhs.e.unify(lhs.sort) match {
                    case Some(unifiedRhs) =>
                      Core.mkEq(lhs.e, unifiedRhs)
                    case None =>
                      unexpected(s"unification failed for LHS/RHS of equality: ${lhs} = ${rhs}", expr)
                  }
                case Z3_decl_kind.Z3_OP_CONST_ARRAY =>
                  val arrayConstant = liftTerm(expr.getArgs()(0).asInstanceOf[LoweredTerm])
                  val arraySort = liftSort(expr.getSort)
                  arraySort.sort match {
                    case Core.ArraySort(dom, range) =>
                      arrayConstant.unify(range) match {
                        case Some(arrayConstantUnified) =>
                          Core.mkConstArray(dom, arrayConstantUnified)
                        case None =>
                          unexpected(s"liftTerm: unifying constant array failed: ${arrayConstant} is the constant but ${range} is the sort", expr)
                      }
                    case _ =>
                      unexpected(s"liftTerm: parsing constant array failed: sort ${arraySort} is not an array", expr)
                  }
                case Z3_decl_kind.Z3_OP_AS_ARRAY =>
                  // (as-array f) --- f is a fun
                  // NOTE: f is translated into an uninterpreted function. We need another
                  // pass to give value to these functions.
                  expr match {
                    case arrE: z3.ArrayExpr[_, _] =>
                      val f = arrE.getArgs()(0).getFuncDecl
                      val fName = f.getName.toString
                      val fDomain = f.getDomain.toList.map(liftSort)
                      val fRange = liftSort(f.getRange)
                      val fSort = liftSort(arrE.getSort)
                      fSort.sort match {
                        case Core.ArraySort(aDom, aRange) =>
                          fRange.unify(aRange) match {
                            case Some(unifiedRange) =>
                              val funcSort = Core.funSort(fDomain, unifiedRange)
                              val arrSort = Core.ArraySort(aDom, unifiedRange)
                              funcMap.update(fName, f.asInstanceOf[LoweredVarDecl])
                              Core.mkAsArray(Core.mkVar(fName, funcSort.unbox()), arrSort)
                            case None =>
                              unexpected("")
                          }
                        case _ => unexpected("")
                      }
                    case _ =>
                      unexpected(s"liftTerm: Z3_OP_AS_ARRAY: cannot parse expression ${expr}", expr)
                  }
                case Z3_decl_kind.Z3_OP_STORE =>
                  // store(arr, idx, val)
                  val args = expr.getArgs
                  val storeArr = liftTerm(args(0).asInstanceOf[LoweredTerm])
                  val storeIdx = liftTerm(args(1).asInstanceOf[LoweredTerm])
                  val storeVal = liftTerm(args(2).asInstanceOf[LoweredTerm])
                  storeArr.unify(Core.ArraySort(storeIdx.sort, storeVal.sort)) match {
                    case Some(unifiedArr) =>
                      Core.mkStore(unifiedArr, storeIdx, storeVal)
                    case None =>
                      unexpected(s"liftTerm: Z3_OP_STORE: unification failed of expression ${storeArr} given index ${storeIdx} and value ${storeVal}", expr)
                  }

                case Z3_decl_kind.Z3_OP_SELECT =>
                  // select(arr, idx) = val
                  val args = expr.getArgs
                  val arr = liftTerm(args(0).asInstanceOf[LoweredTerm])
                  val idx = liftTerm(args(1).asInstanceOf[LoweredTerm])
                  arr.sort match {
                    case a@Core.ArraySort(dom, range) =>
                      arr.unify(Core.ArraySort(idx.sort, range)) match {
                        case Some(unifiedArr) =>
                          Core.mkSelect(unifiedArr, idx.e)
                        case None =>
                          unexpected(s"liftTerm: arr ${arr.toString} does not match index sort ${idx.toString}", expr)
                      }
                    case _ =>
                      unexpected(s"liftTerm: array ${arr.toString} is not an array expression", expr)
                  }
                case Z3_decl_kind.Z3_OP_ARRAY_MAP =>
                  //     public final <D extends Sort, R1 extends Sort, R2 extends Sort> ArrayExpr<D, R2> mkMap(FuncDecl<R2> f, Expr<ArraySort<D, R1>>... args)
                  unsupported("Err: Z3_OP_ARRAY_MAP unsupported")
                case Z3_decl_kind.Z3_OP_ARRAY_DEFAULT =>
                  unsupported("Err: Z3_OP_ARRAY_DEFAULT unsupported")
                case Z3_decl_kind.Z3_OP_ARRAY_EXT =>
                  unsupported("Err: Z3_OP_ARRAY_EXT unsupported")
                case Z3_decl_kind.Z3_OP_DT_CONSTRUCTOR =>
                  val constructor = expr.getFuncDecl
                  rangeSort.sort match {
                    case sortT: Core.DatatypeConstructorSort =>
                      sortT.lookupConstructor(constructor.getName.toString) match {
                        case Some(dtc) =>
                          parseZ3Constructor(constructor, expr.getArgs.toList.map(x => x.asInstanceOf[LoweredTerm]), dtc) match {
                            case Some(ic) =>
                              Core.mkDatatypeAccessor(sortT, ic)
                            case None =>
                              unexpected(s"Err: Z3_OP_DT_CONSTRUCTOR: cannot parse constructor ${constructor.toString}", expr)
                          }
                        case None =>
                          unexpected(s"Err: Z3_OP_DT_CONSTRUCTOR: constructor ${constructor.getName.toString} not found in sort ${sortT}", expr)
                      }
                    case sortT: Core.FiniteUniverseSort =>
                      // Z3 implements finite universe sorts as enum sorts (datatypes with nullary constructors)
                      // Constructor names have the pattern: elt_<index>_fd_<sortName>
                      val constructorName = constructor.getName.toString
                      val pattern = raw"elt_(\d+)_fd_.*".r
                      constructorName match {
                        case pattern(indexStr) =>
                          val index = indexStr.toInt
                          Core.mkConst(Core.SortValue.FiniteUniverseValue(index, sortT))
                        case _ =>
                          unexpected(s"Err: Z3_OP_DT_CONSTRUCTOR: finite universe constructor name '${constructorName}' does not match expected pattern", expr)
                      }
                    case _ =>
                      unexpected(s"Err: Z3_OP_DT_CONSTRUCTOR but ${constructor.toString} has sort ${rangeSort} which is neither datatype nor finite universe", expr)
                  }
                case Z3_decl_kind.Z3_OP_FD_CONSTANT =>
                  unsupported("Z3_OP_FD_CONSTANT reached, but finite-domain sorts are implemented using DatatypeSorts in Z3 now, so unsupported")
                case Z3_decl_kind.Z3_OP_DT_IS | Z3_decl_kind.Z3_OP_DT_RECOGNISER =>
                  val arg = liftTerm(expr.getArgs()(0).asInstanceOf[LoweredTerm])
                  val sort = liftSort(expr.getFuncDecl.getDomain()(0))
                  val constructorName = expr.getFuncDecl.getName.toString.stripPrefix("is-")
                  sort match {
                    case dt: Core.DatatypeConstructorSort =>
                      arg.unify(dt) match {
                        case Some(unifiedArg) =>
                          Core.mkDatatypeRecognizer(dt, constructorName, unifiedArg)
                        case None =>
                          unexpected(s"liftTerm: Z3_OP_DT_IS/RECOGNIZER: sort ${dt} cannot be unified against ${arg}", expr)
                      }
                    case _ =>
                      unexpected(s"liftTerm: Z3_OP_DT_IS/RECOGNISER: sort ${sort} is not a datatype sort", expr)
                  }
                case Z3_decl_kind.Z3_OP_DT_ACCESSOR =>
                  val args = expr.getArgs.toList.map(x => x.asInstanceOf[LoweredTerm]).map(liftTerm)
                  val constructorName = expr.getFuncDecl.getName.toString
                  val accessorDomain = expr.getFuncDecl.getDomain
                  val sort =
                    if accessorDomain.isEmpty then
                      unexpected(s"liftTerm: Z3_OP_DT_ACCESSOR: accessor ${constructorName} has empty domain", expr)
                    else
                      liftSort(accessorDomain(0))
                  sort match {
                    case dt: Core.DatatypeConstructorSort =>
                      dt.lookupConstructor(constructorName) match {
                        case Some(ct) =>
                          val ic = Core.instantiatedConstructor(ct, args)
                          Core.mkDatatypeAccessor(dt, ic)
                        case None =>
                          unexpected(s"liftTerm: Z3_OP_DT_ACCESSOR: constructor ${constructorName} not found in datatype ${dt}", expr)
                      }
                    case _ =>
                      unexpected(s"liftTerm: Z3_OP_DT_ACCESSOR: constructor sort is ${sort} but not a datatype constructor sort", expr)
                  }
                case Z3_decl_kind.Z3_OP_DT_UPDATE_FIELD =>
                  unsupported("datatype field updates in Z3 are outside of SMTLIB standard and not supported. See https://microsoft.github.io/z3guide/docs/theories/Datatypes/")
                case Z3_decl_kind.Z3_OP_ADD =>
                  val args = expr.getArgs.map(x => x.asInstanceOf[LoweredTerm]).toList.map(liftTerm)
                  Core.unifyTerms(args, Core.NumericSort()) match {
                    case Some(unifiedArgs) =>
                      Core.mkAdd(unifiedArgs)
                    case None =>
                      unexpected(s"unification failed on addition: (+ ${args.mkString(", ")})", expr)
                  }
                case Z3_decl_kind.Z3_OP_SUB =>
                  val lhs = liftTerm(expr.getArgs()(0).asInstanceOf[LoweredTerm])
                  val rhs = liftTerm(expr.getArgs()(1).asInstanceOf[LoweredTerm])
                  (lhs.unify(Core.NumericSort()), rhs.unify(Core.NumericSort())).tupled match {
                    case Some(unifiedLhs, unifiedRhs) =>
                      Core.mkMinus(unifiedLhs, unifiedRhs)
                    case None =>
                      unexpected(s"unification failed on subtraction: (- ${lhs} ${rhs})", expr)
                  }
                case Z3_decl_kind.Z3_OP_UMINUS =>
                  val subExpr = expr.getArgs()(0).asInstanceOf[LoweredTerm]
                  val subExprT = liftTerm(subExpr)
                  subExprT.unify(Core.NumericSort()) match {
                    case Some(unifiedSubExpr) =>
                      Core.mkNegative(unifiedSubExpr)
                    case None =>
                      unexpected(s"unification failed on numerical negation: (- ${subExprT})", expr)
                  }
                case Z3_decl_kind.Z3_OP_MUL =>
                  val args = expr.getArgs.map(x => x.asInstanceOf[LoweredTerm]).toList
                  failwith("liftTerm: multiplication not yet supported")
                case Z3_decl_kind.Z3_OP_DIV =>
                  unsupported("liftTerm: division not yet supported")
                case Z3_decl_kind.Z3_OP_UNINTERPRETED => // TODO: Z3_OP_UNINTERPRETED doesn't necessarily mean it is an uninterpreted sort.
                  liftSort(expr.getSort) match {
                    case uSort: Core.UnInterpretedSort =>
                      val funcDecl = expr.getFuncDecl
                      val name = funcDecl.getName.toString
                      funcMap.update(name, funcDecl)
                      Core.mkConst(Core.uninterpreted(name, uSort))
                    case _ =>
                      if domainSorts.isEmpty then {
                        val name = decl.getName.toString
                        funcMap.update(name, decl)
                        Core.mkVar(name, rangeSort)
                      } else {
                        val funcName = expr.getFuncDecl.getName
                        val funcSort = Core.funSort(expr.getFuncDecl.getDomain.toList.map(liftSort), liftSort(expr.getFuncDecl.getRange).sort)
                        val func = interpEnv(funcName.toString).getOrElse(unexpected(s"Error: applying function not-found ${funcName.toString}"))
                        funcSort.unify(func.sort) match {
                          case Some(_) =>
                            func.e match {
                              case mac@Core.Macro(name, vars, bodyExpr) =>
                                val varsEnv = vars.toArray
                                val funcArgs = expr.getArgs.zipWithIndex.map((x, i) =>
                                  if x.isVar then {
                                    val boundVarIdx = x.getIndex
                                    val sort = liftSort(x.getSort).sort
                                    // deBruijnStack(i) is the i-th indexed variable name.
                                    assert(deBruijnStack.size > boundVarIdx)
                                    val varName = deBruijnStack(boundVarIdx)
                                    (varName, Core.mkVar(varName, sort).box())
                                  } else {
                                    (varsEnv(i)._1, liftTerm(x.asInstanceOf[LoweredTerm]))
                                  }).toList
                                Core.mkApp(funcArgs, mac)
                              case v@Core.Var(name, _) =>
                                val funcArgs = expr.getArgs.zipWithIndex.map((x, i) =>
                                  if x.isVar then {
                                    val boundVarIdx = x.getIndex
                                    val sort = liftSort(x.getSort).sort
                                    // deBruijnStack(i) is the i-th indexed variable name.
                                    assert(deBruijnStack.size > boundVarIdx)
                                    val varName = deBruijnStack(boundVarIdx)
                                    (varName, Core.mkVar(varName, sort).box())
                                  } else {
                                    (s"arg$i", liftTerm(x.asInstanceOf[LoweredTerm]))
                                  }).toList
                                Core.mkApp(funcArgs, Core.mkVar(funcName.toString, funcSort))
                              case _ => unexpected(s"error: got ${func}")
                            }
                          case None => unexpected(s"Error: applying a non-function: ${}")
                        }
                      }
                  }
                case _ =>
                  unsupported(s"Unrecognized expression: ${expr.toString} with decl type ${declKind}", expr)
              }
            }

            decodeDeclByKind()
          }
      }
    }

    // From Z3_sort_kind.java:
    //    Z3_UNINTERPRETED_SORT (0),
    //    Z3_BOOL_SORT (1),
    //    Z3_INT_SORT (2),
    //    Z3_REAL_SORT (3),
    //    Z3_BV_SORT (4),
    //    Z3_ARRAY_SORT (5),
    //    Z3_DATATYPE_SORT (6),
    //    Z3_RELATION_SORT (7),
    //    Z3_FINITE_DOMAIN_SORT (8),
    //    Z3_FLOATING_POINT_SORT (9),
    //    Z3_ROUNDING_MODE_SORT (10),
    //    Z3_SEQ_SORT (11),
    //    Z3_RE_SORT (12),
    //    Z3_CHAR_SORT (13),
    //    Z3_TYPE_VAR (14),
    //    Z3_UNKNOWN_SORT (1000);
    private def resolveZ3SortKind(z3SortKind: Z3_sort_kind): String = {
      z3SortKind match {
        case Z3_sort_kind.Z3_UNINTERPRETED_SORT => "Z3_UNINTERPRETED_SORT"
        case Z3_sort_kind.Z3_BOOL_SORT => "Z3_BOOL_SORT"
        case Z3_sort_kind.Z3_INT_SORT => "Z3_INT_SORT"
        case Z3_sort_kind.Z3_BV_SORT => "Z3_BV_SORT"
        case Z3_sort_kind.Z3_ARRAY_SORT => "Z3_ARRAY_SORT"
        case Z3_sort_kind.Z3_DATATYPE_SORT => "Z3_DATATYPE_SORT"
        case Z3_sort_kind.Z3_RELATION_SORT => "Z3_RELATION_SORT"
        case Z3_sort_kind.Z3_FLOATING_POINT_SORT => "Z3_FLOATING_POINT_SORT"
        case Z3_sort_kind.Z3_ROUNDING_MODE_SORT => "Z3_ROUNDING_MODE_SORT"
        case Z3_sort_kind.Z3_SEQ_SORT => "Z3_SEQ_SORT"
        case Z3_sort_kind.Z3_RE_SORT => "Z3_RE_SORT"
        case Z3_sort_kind.Z3_CHAR_SORT => "Z3_CHAR_SORT"
        case Z3_sort_kind.Z3_TYPE_VAR => "Z3_TYPE_VAR"
        case Z3_sort_kind.Z3_UNKNOWN_SORT => "Z3_UNKNOWN_SORT"
        case Z3_sort_kind.Z3_FINITE_DOMAIN_SORT => "Z3_FINITE_DOMAIN_SORT"
        case Z3_sort_kind.Z3_REAL_SORT => "Z3_REAL_SORT"
      }
    }

    override def liftSort(sort: z3.Sort): BoxedSort = {
      val sortName = sort.getName.toString
      val sortKind = sort.getSortKind
      sortKind match {
        case Z3_sort_kind.Z3_UNINTERPRETED_SORT =>
          val bs = typeEnv(sortName).getOrElse(unexpected(s"liftSort: sort ${sortName} not found in type environment"))
          bs.sort match {
            case _: Core.UnInterpretedSort =>
              bs
            case _ =>
              unexpected(s"liftSort: Z3 sort and IR sort mismatch: IR sort is ${bs} but Z3 sort is ${resolveZ3SortKind(sortKind)}", sort)
          }
        case Z3_sort_kind.Z3_BOOL_SORT =>
          Core.BoolSort()
        case Z3_sort_kind.Z3_ARRAY_SORT =>
          sort match {
            case arrS: z3.ArraySort[d, r] =>
              val domSort = liftSort(arrS.getDomain)
              val rangeSort = liftSort(arrS.getRange)
              Core.arraySort(domSort, rangeSort)
            case _ =>
              unexpected(s"liftSort: sort ${sortName} has ambiguous Z3 AST type: sortKind is ${resolveZ3SortKind(sortKind)} which disagrees with AST type", sort)
          }
        case (Z3_sort_kind.Z3_DATATYPE_SORT) =>
          typeEnv(sortName) match {
            case Some(bs) =>
              bs.sort match {
                case _: DatatypeConstructorSort => bs
                case _: FiniteUniverseSort => bs
                case _ => unexpected(s"liftSort: Z3 sort and IR sort mismatch: IR sort is ${bs} but Z3 sort is ${resolveZ3SortKind(sortKind)}", sort)
              }
            case None =>
              unexpected(s"liftSort: sort ${sortName} not found in type environment", sort)
          }
        case (Z3_sort_kind.Z3_INT_SORT) =>
          Core.NumericSort()
        case _ =>
          unsupported(s"liftSort: cannot handle Z3 sort, sort " +
            s" kind is ${resolveZ3SortKind(sortKind)}", sort)
      }
    }

    override def liftFunc(z3Func: FuncDecl[z3.Sort]): BoxedExpr = {
      val z3FuncName = z3Func.getName.toString
      val z3FuncDom = z3Func.getDomain.toList
      val z3FuncRange = z3Func.getRange

      val domSorts = z3FuncDom.map(liftSort)
      val rangeSort = liftSort(z3FuncRange)

      val sort = Core.funSort(domSorts, rangeSort)
      val uf = Core.mkVar(z3FuncName, sort)
      funcMap.update(z3FuncName, z3Func)
      uf
    }


    override def declareVar[S <: Core.Sort[S]](v: String, s: S): LoweredVarDecl = {
      s match {
        case fsort@Core.FunSort(_, _) =>
          funcMap.get(v) match {
            case Some(funcDecl) => funcDecl
            case None =>
              // No FuncDecl created previously for f. Declare it.case _: scala.Some[_] => ???
              val domSorts = fsort.domainSort.map(x => lowerSort(x))
              val rangeSort = lowerSort(fsort.rangeSort)
              val fFuncDecl = context.mkFuncDecl(v, domSorts.toArray, rangeSort)
              funcMap.update(v, fFuncDecl)
              fFuncDecl
          }
        case _ =>
          val z3Sort = lowerSort(s)
          funcMap.get(v) match {
            case Some(fDecl) =>
              fDecl
            case None =>
              val x = context.mkFuncDecl(v, Array[z3.Sort](), z3Sort)
              funcMap.update(v, x)
              assert(funcMap(v) == x)
              x
          }
      }
    }

    override def defineVar[S <: Core.Sort[S]](v: String, s: S, e: Core.Expr[S]): (LoweredVarDecl, List[LoweredTerm]) = {
      appendHistory(s"defineVar(${v}, ${s.toString}, ${e.toString})")
      val funcDecl = declareVar(v, s)
      axiomMap.get(v) match {
        case Some(_) => unexpected("")
        case None => {
          val axioms = (s, e) match {
            case (fsort@Core.FunSort(_, range), m@Macro(name, domain, body)) =>
              // add axiom
              // forall X'. f(X') = body [X <- X']
              val forallAxiom =
                Core.mkForall(
                  domain,
                  Core.mkEq(
                    Core.mkSubst("app",
                      domain.map(x => (x._1, Core.mkVar(x._1, x._2))),
                      Core.mkVar(v, Core.toFunSort(domain, range))
                    ),
                    body
                  )
                )
              val z3Expr = lower(forallAxiom).asInstanceOf[LoweredTerm]
              List(z3Expr)
            case (_: Core.FunSort[?], Var(_, _)) => List()
            case (_, Var(_, _)) => List()
            case _ =>
              val z3Expr = lower(e)
              List(context.mkEq(funcDecl.apply(), z3Expr).asInstanceOf[LoweredTerm])
          }
          axioms.foreach(axiom => this.solver.add(axiom.asInstanceOf[z3.Expr[z3.BoolSort]]))
          (funcDecl, axioms)
        }
      }
    }

    override def lookupDecl[S <: Core.Sort[S]](v: String, s: S): Option[LoweredVarDecl] = {
      try
        Some(this.funcMap(v))
      catch
        case _ => None
    }


    override def initialize(l: SmtSolver.Logic): Unit = {
      reset()
    }


    override def defineConst[S <: Core.Sort[S]](v: Core.SortValue[S]): LoweredTerm = {
      appendHistory(s"defineConst(${v.toString})")
      lowerValue(v)
    }

    override def add(fs: List[Core.BoxedExpr]): List[LoweredTerm] = {
      appendHistory(s"add(${fs.map(_.toString).mkString(" ")})")
      val loweredExprs = fs.map(x => lower(x.e))
      loweredExprs.foreach(x => solver.add(x.asInstanceOf[z3.BoolExpr]))
      loweredExprs
    }

    override def addTerms(terms: List[LoweredTerm]): List[LoweredTerm] = {
      appendHistory(s"addTerms(${terms.map(_.toString).mkString(" ")})")
      terms.foreach(x => solver.add(x.asInstanceOf[z3.BoolExpr]))
      terms
    }


    override def push(): Unit = {
      appendHistory("push()")
      solver.push()
    }

    override def pop(): Unit = {
      appendHistory("pop()")
      solver.pop()
    }

    override def reset(): Unit = {
      appendHistory("reset()")
      solver.reset()
    }

    override def checkSat(): SmtSolver.Result = {
      appendHistory("checkSat()")
      solver.check() match {
        case Status.SATISFIABLE => Result.SAT
        case Status.UNKNOWN => Result.UNKNOWN
        case Status.UNSATISFIABLE => Result.UNSAT
      }
    }

    override def getModel: Option[Z3Model] = {
      appendHistory("getModel()")
      try {
        val m = solver.getModel
        if (m == null) None
        else Some(new Z3Model(m, this, enableCompletion = true))
      } catch {
        case _ =>
          None
      }
    }

    override def getUnsatCore: Option[Z3UnsatCore] = {
      appendHistory("getUnsatCore()")
      val core = solver.getUnsatCore
      println(s"Z3 --- getUnsatCore --- ${core.map(x => x.toString).mkString("Array(", ", ", ")")}")
      core match {
        case _ if core.equals(null) || core.toString.equals("null") => None
        case Array() => None
        case _ => Some(Z3UnsatCore(core.toSet, this))
      }
    }
  }


  class Z3UnsatCore(val coreTerms: Set[z3.BoolExpr], solver: Z3Solver.Z3Solver)
    extends SmtSolver.UnsatCore[z3.Expr[z3.Sort], z3.FuncDecl[z3.Sort]](solver) {

    override def terms(): Set[Expr[Sort]] = {
      coreTerms.map(x => x.asInstanceOf[z3.Expr[z3.Sort]])
    }

    override def formulas(): Set[Core.Expr[BoolSort]] = {
      coreTerms.map(x =>
        solver.liftTerm(x.asInstanceOf[z3.Expr[z3.Sort]]).unify(Core.BoolSort()).get
      )
    }
  }


  class Z3Model(
                 val model: z3.Model,
                 solver: Z3Solver.Z3Solver,
                 val enableCompletion: Boolean = false
               ) extends SmtSolver.Model[z3.Expr[z3.Sort], z3.FuncDecl[z3.Sort]](solver) {
    type T = Z3Model

    override def formula(): Core.Expr[Core.BoolSort] = {
      val z3Term = asTerm()
      val expr = solver.liftTerm(z3Term)
      expr.unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"Z3Model.formula(): Expression constructed from model is ${expr}, which does not return a boolean.")
      }
    }

    override def formula(vocab: Set[(String, BoxedSort)]): Core.Expr[Core.BoolSort] = {
      val z3Term = asTerm(vocab)
      println(s"formula(...): z3 term of model is ${z3Term.toString}")
      val expr = solver.liftTerm(z3Term)
      expr.unify(Core.BoolSort()) match {
        case Some(unifiedExpr) => unifiedExpr
        case None => failwith(s"Z3Model.formula(V): Expression constructed from model is ${expr}, which does not return a boolean.")
      }
    }

    override def valueOf[S <: Core.Sort[S]](name: String, sort: S): Option[Core.Expr[S]] = {
      sort match {
        case f: Core.FunSort[t] =>
          None // Functions do not have a value, they only have an axiom via asTerm / asNegatedTerm / formula
        case _ =>
          val someExpr = evaluate(Core.mkVar(name, sort))
          someExpr.unify(sort) match {
            case Some(unifiedExpr) => Some(unifiedExpr)
            case None => None
          }
      }
    }

    override def vocabulary(): (List[BoxedSort], List[String]) = {
      val sortDecls = model.getSorts.toList
      val constDecls = model.getConstDecls.toList
      val constNames = constDecls.map(x => x.getName.toString)
      val sorts = sortDecls.map(x => solver.liftSort(x))
      (sorts, constNames)
    }

    override def evaluate[S <: Core.Sort[S]](e: Core.Expr[S]): Core.Expr[S] = {
      val term = solver.lower(e)
      val t = model.evaluate(term, enableCompletion)
      val be = solver.liftTerm(t)
      be.unify(e.sort) match {
        case Some(ue) => ue
        case None => unexpected(s"model.evaluate: got term ${be}, which is of not of sort ${e.sort} for ${e}")
      }
    }

    override def asNegatedTerm(): this.solver.LoweredTerm = {
      val context = solver.getContext

      val constDecls = model.getConstDecls.toList

      val declEqualities: List[z3.Expr[z3.Sort]] =
        constDecls.map { decl =>
          context.mkEq(decl.apply(), model.getConstInterp(decl)).asInstanceOf[z3.Expr[z3.Sort]]
        }

      val conjunct =
        declEqualities match {
          case Nil => context.mkTrue()
          case head :: tail =>
            context.mkAnd(declEqualities.map(x => x.asInstanceOf[z3.Expr[z3.BoolSort]]).toArray *)
        }

      context.mkNot(conjunct).asInstanceOf[z3.Expr[z3.Sort]]
    }

    //
    // A constDecl yields a term in the formula representation of the model, whereas
    // a function declration yields a FuncInterp, which gets translated into a forall axiom.
    //
    private[smt] def funcInterpToAxiom(fv: FuncDecl[z3.Sort], fi: FuncInterp[z3.Sort]): z3.BoolExpr = {
      val ctx = solver.getContext
      val arity = fv.getArity
      val domainSorts = fv.getDomain

      val entryEqualities: Array[z3.BoolExpr] =
        fi.getEntries.map { entry =>
          val groundArgs = entry.getArgs
          val entryValue = entry.getValue
          ctx.mkEq(ctx.mkApp(fv, groundArgs *), entryValue)
        }

      val elseClause: Option[z3.BoolExpr] =
        Option(fi.getElse).map { elseValue =>
          if arity == 0 then
            ctx.mkEq(fv.apply(), elseValue)
          else {
            val boundVars: IndexedSeq[z3.Expr[z3.Sort]] =
              (0 until arity).map { i =>
                // ctx.mkBound(arity - 1 - i, domainSorts(i))
                ctx.mkBound(i, domainSorts(i))
              }

            val matchClauses: Array[z3.BoolExpr] =
              fi.getEntries.map { entry =>
                val groundArgs = entry.getArgs
                val equalities =
                  (0 until arity).map { idx =>
                    ctx.mkEq(boundVars(idx), groundArgs(idx)).asInstanceOf[z3.BoolExpr]
                  }
                if equalities.isEmpty then ctx.mkTrue()
                else if equalities.length == 1 then equalities.head
                else ctx.mkAnd(equalities.toArray *)
              }

            val guard: z3.BoolExpr =
              if matchClauses.isEmpty then ctx.mkTrue()
              else {
                val disjunction =
                  if matchClauses.length == 1 then matchClauses.head
                  else ctx.mkOr(matchClauses.toArray *)
                ctx.mkNot(disjunction)
              }

            val applied =
              ctx.mkApp(fv, boundVars.toArray *)

            val equality =
              ctx.mkEq(applied, elseValue)

            val body =
              if matchClauses.isEmpty then equality
              else ctx.mkImplies(guard, equality)

            // println(s" *** funcInterp parser: matchClauses [ ${matchClauses.mkString(", ")} ]")
            // println(s" *** funcInterp parser: equality ${equality.toString}")
            // println(s" *** funcInterp parser: body ***\n${body.toString}\n***")


            val names = (0 until arity).map(i => ctx.mkSymbol(s"arg_$i").asInstanceOf[com.microsoft.z3.Symbol]).toArray

            val ret = ctx.mkForall(domainSorts, names, body, 0, null, null, null, null)
            // println(s" *** funcInterp parser: map result ${ret}")
            ret
          }
        }
      val conjuncts = entryEqualities.toList ++ elseClause.toList

      conjuncts match {
        case Nil =>
          ctx.mkTrue()
        case single :: Nil =>
          single
        case many =>
          ctx.mkAnd(many.toArray *)
      }
    }

    override def asNegatedTerm(vocab: Set[(String, BoxedSort)]): this.solver.LoweredTerm = {
      val context = solver.getContext
      val conjunct = asTerm(vocab).asInstanceOf[z3.BoolExpr]
      context.mkNot(conjunct).asInstanceOf[z3.Expr[z3.Sort]]
    }

    override def asTerm(vocab: Set[(String, BoxedSort)]): solver.LoweredTerm = {
      val context = solver.getContext
      val declEqualities: List[z3.BoolExpr] =
        vocab.map { case (name, sort) =>
          sort.sort match {
            case f: Core.FunSort[t] =>
              this.solver.lookupDecl(name, sort) match {
                case Some(decl) =>
                  Option(this.model.getFuncInterp(decl)) match {
                    case Some(funcInterp) =>
                      funcInterpToAxiom(decl, funcInterp)
                    case None =>
                      context.mkTrue()
                  }
                case None =>
                  failwith(s"error: declaration of ${name} not found in solver object")
              }
            case _ =>
              val c = context.mkConst(name, solver.lowerSort(sort))
              val evaluationResult = model.evaluate(c, enableCompletion)
              context.mkEq(c, evaluationResult)
          }
        }.toList

      val conjunct =
        declEqualities match {
          case Nil => context.mkTrue()
          case _ => context.mkAnd(declEqualities.toArray *)
        }

      conjunct.asInstanceOf[z3.Expr[z3.Sort]]
    }

    override def asTerm(): solver.LoweredTerm = {
      val constDecls = model.getConstDecls.toList
      val equalities =
        solver.getContext.mkAnd(constDecls.map(
          x =>
            (solver.getContext.mkEq(x.apply(), model.getConstInterp(x)))
        ).toArray *)
      val funcDecls = model.getFuncDecls.toList
      val funcAxioms =
        funcDecls.map(funcDecl =>
          val funcInterp = model.getFuncInterp(funcDecl)
          funcInterpToAxiom(funcDecl.asInstanceOf[FuncDecl[z3.Sort]], funcInterp.asInstanceOf[FuncInterp[z3.Sort]])
        )

      solver.getContext.mkAnd((equalities :: funcAxioms).toArray *).asInstanceOf[solver.LoweredTerm]
    }


    override def toString: String = {
      "Z3 Model {" + this.model.toString + "}"
    }

    override def apply(arg: String, sort: BoxedSort): Option[BoxedExpr] = {
      val c = solver.getContext.mkConst(arg, solver.lowerSort(sort))
      Some(solver.liftTerm(model.evaluate(c, enableCompletion)))
    }
  }
}
