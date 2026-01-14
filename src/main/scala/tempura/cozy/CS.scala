package tempura.cozy

import clojure.lang.{Symbol, *}
import tempura.expression.Core
import tempura.helpers.Utils.unexpected
import tempura.cozy.CozyExpr
import tempura.parsing.sexpr.{ParseTree, SmtlibParser, StringToSExprParser, TDLParser}
import tempura.expression.Syntax.*
import tempura.helpers.Utils.*

import scala.collection.mutable.{ListBuffer, HashMap as HM}
import scala.annotation.static
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import clojure.lang.RT.`var` as rt_var
import tempura.cozy.CozyExpr.{CKeyword, CSeq, CSymbol}
import tempura.expression.Core.BoxedExpr
import tempura.parsing.io.{PathOf, StringReader}
import tempura.smt.{Cvc5Solver, SmtSolver, Z3Solver}
import tempura.smt.SmtInterpolSolver.SmtInterpolSolver
import tempura.smt.SmtSolver.{Result, SolverEnvironment}

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

  // register some library functions with Clojure runtime

  final private val COZY_NAMESPACE = "c"
  final private val COZY_SOLVER_NAMESPACE = "c.solver"
  final private val COZY_SOLVER_OPS_NAMESPACE = "c.solverOps"
  final private val COZY_TRANSFORM_NAMESPACE = "c.transforms"
  
  CozyFunction.cozyFunction1("sort", COZY_NAMESPACE) {
    arg =>
      import CozyExpr.*
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)

      convert(arg) match {
        case CSymbol(sortName, sortNs) =>
          val sortNamespace = if sortNs == null then "user" else sortNs
          if getCurrentNsName != sortNamespace then {
            println(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${sortNamespace}, not current namespace ${getCurrentNsName}.")
          }
          ENV.get(sortNamespace) match {
            case Some(ns) =>
              typeEnv |- Core.UnInterpretedSort(sortName, 0)
              println(s"Cozy: Creating uninterpreted sort $sortName in namespace $sortNamespace")
            case None =>
              println(s"Cozy: coult not find namespace ${sortNamespace}")
          }
          rt_var(getCurrentNsName, sortName, typeEnv(sortName).get)
        case _ => failwith("Cozy error: sort takes a quoted name")
      }
  }

  CozyFunction.cozyFunction2("finite-sort", COZY_NAMESPACE) {
    (arg1, arg2) =>
      import CozyExpr.*
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)

      (convert(arg1), convert(arg2)) match {
        case (CSymbol(sortName, sortNs), CInt(sz)) =>
          val sortNamespace = if sortNs == null then "user" else sortNs
          if getCurrentNsName != sortNamespace then {
            println(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${sortNamespace}, not current namespace ${getCurrentNsName}.")
          }
          ENV.get(sortNamespace) match {
            case Some(ns) =>
              typeEnv |- Core.FiniteUniverseSort(sortName, sz.toInt)
              println(s"Cozy: Creating finite sort $sortName of size ${sz.toInt}")
            case None =>
              println(s"Cozy: could not find sort namespace $sortNamespace")
          }
          rt_var(getCurrentNsName, sortName, typeEnv(sortName).get)
        case _ => failwith(s"Cozy error: malformed arguments ${(arg1, arg2)} to finite-sort")
      }
  }

  CozyFunction.cozyFunction2("var", COZY_NAMESPACE) {
    (arg0, arg1) =>
      import CozyExpr.*
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
      (convert(arg0), convert(arg1)) match {
        case (CSymbol(varName, varNs), sortExpr) =>
          val output = new ListBuffer[String]()
          val varNamespace = if varNs == null then "user" else varNs
          if getCurrentNsName != varNamespace then {
            output.addOne(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${varNamespace}, not current namespace ${getCurrentNsName}.")
          }

          ENV.get(varNamespace) match {
            case Some(ns) =>
              CozyToFormula.cozyParseSort(sortExpr) match {
                case Right(s) =>
                  interpEnv |- (varName, s)
                  output.addOne(s"Cozy: Creating variable $varName of sort $s in namespace $varNamespace")
                case Left(err) =>
                  output.addOne(s"Cozy: error encountered creating variable ${err}")
              }
            case None =>
              failwith(s"Cozy: Error: ${varNamespace} not found.")
          }
          println(output.toList.mkString("\n"))
          RT.`var`(getCurrentNsName, varName, interpEnv(varName).get)
        case (_, _) => failwith(s"Cozy error: illegal arguments to c-var ${(arg0, arg1)}")
      }
  }

  CozyFunction.cozyFunction1("expr", COZY_NAMESPACE) {
    arg => 
      import CozyExpr.*
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
      CozyToFormula.cozyParseExpr(convert(arg)) match {
        case Right(t) => t
        case Left(err) => failwith(s"Cozy error: ${err}")
      }
  }
  
  CozyFunction.cozyFunction2("def", COZY_NAMESPACE) {
    (arg0, arg1) =>
      import CozyExpr.*
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
      (convert(arg0), convert(arg1)) match {
        case (CSymbol(varName, varNs), defExpr) =>
          val varNamespace = if varNs == null then "user" else varNs
          if getCurrentNsName != varNamespace then {
            println(s"Cozy: Warning: You're creating a shadow-state variable in namespace ${varNamespace}, not current namespace ${getCurrentNsName}.")
          }
          ENV.get(varNamespace) match {
            case Some(ns) =>
              CozyToFormula.cozyParseExpr(defExpr) match {
                case Right(exp) =>
                  interpEnv ||- (varName, exp)
                  rt_var(varNamespace, varName, exp)
                  println(s"Cozy: Creating definition $varName = $exp in namespace $varNamespace")
                case Left(err) =>
                  println(s"Cozy: error encountered creating variable ${err}")
              }
            case None =>
              failwith(s"Cozy: Error: ${varNamespace} not found.")
          }
          rt_var(getCurrentNsName, varName, interpEnv(varName).get)
        case (_, _) => failwith(s"Cozy error: illegal arguments to c-var ${(arg0, arg1)}")
      }
  }
  
  CozyFunction.cozyFunction2("create", COZY_SOLVER_NAMESPACE) {
    (arg0, arg1) =>
      val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
      (convert(arg0), convert(arg1)) match {
        case (CSymbol(solverName, solverNamespace), CKeyword(solverNickName, _)) =>
          val solverNs = if solverNamespace == null then "user" else solverNamespace
          val (typeEnv, interpEnv) = (currentNS.getTypeEnv, currentNS.getInterpEnv)
          solverName match {
            case "z3" =>
              val slv = Z3Solver.Z3Solver(typeEnv, interpEnv)
              currentNS.addSolverEnv(solverNickName, slv.box)
              println(s"Cozy: Solver ${solverNickName} for z3 added to current namespace")
            case "cvc5" =>
              val slv = Cvc5Solver.Cvc5Solver(typeEnv, interpEnv)
              currentNS.addSolverEnv(solverNickName, slv.box)
              println(s"Cozy: Solver ${solverNickName} for cvc5 added to current namespace")
            case "smtinterpol" =>
              val slv = SmtInterpolSolver(typeEnv, interpEnv)
              currentNS.addSolverEnv(solverNickName, slv.box)
              println(s"Cozy: Solver ${solverNickName} for smtinterpol added to current namespace")
            case e =>
              println(s"Cozy: Solver can only be one of {z3, cvc5, smtinterpol}, but got ${e}.")
          }
          rt_var(getCurrentNsName, solverNickName, currentNS.solvers(solverNickName))
        case (a, b) => failwith(s"Cozy error: got illegal arguments ${(a, b)} in create-solver")
      }
  }

  CozyFunction.cozyFunction("interp-env", COZY_SOLVER_NAMESPACE) { () =>
     currentNS.getInterpEnv
  }

  CozyFunction.cozyFunction("type-env", COZY_SOLVER_NAMESPACE) { () =>
     currentNS.getTypeEnv
  }

  Registry.getAllTransforms foreach {
    (key, transform) =>
      println(s"registering transform $key")
      CozyFunction.cozyFunctionVariadic(key, COZY_TRANSFORM_NAMESPACE) {
        args => transform.applyUntyped(args.toList)
      }
  }
  
  /////////////////////////////////////////////////////////////////////
  /////////////////////////// SMT solver operations
  /////////////////////////////////////////////////////////////////////
  CozyFunction.cozyFunction1("push", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].solver.push()
    null
  }

  CozyFunction.cozyFunction1("pop", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].solver.pop()
    null
  }

  CozyFunction.cozyFunction1("reset", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].solver.reset()
    null
  }

  // Adding constraints
  CozyFunction.cozyFunction2("add-constraint", COZY_SOLVER_NAMESPACE) { (solverEnv, expr) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val boxedExpr = expr.asInstanceOf[BoxedExpr]
    solver.add(List(boxedExpr))
  }

  CozyFunction.cozyFunction2("add-constraints", COZY_SOLVER_NAMESPACE) { (arg0, arg1) =>
    arg1 match {
      case i: ISeq =>
        val parsedConstraints = iseq2vec(i).map(x => x.asInstanceOf[BoxedExpr])
        if parsedConstraints.isEmpty then failwith("add-constraints requires at least a solver argument")
        val solver = arg0.asInstanceOf[SolverEnvironment].solver
        val exprs = parsedConstraints.toList
        solver.add(exprs)
      case _ =>
        failwith("add-constraints: argument 2 needs to be a list of constraints")
    }
  }

  // Satisfiability checking
  CozyFunction.cozyFunction1("check-sat", COZY_SOLVER_NAMESPACE) { solverEnv =>
    val result = solverEnv.asInstanceOf[SolverEnvironment].solver.checkSat()
    result match {
      case Result.SAT => Keyword.intern("sat")
      case Result.UNSAT => Keyword.intern("unsat")
      case Result.UNKNOWN => Keyword.intern("unknown")
    }
  }

  CozyFunction.cozyFunction2("c-solver-solve-once", "user") { (solverEnv, expr) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val boxedExpr = expr.asInstanceOf[BoxedExpr]
    val result = boxedExpr.sort match {
      case Core.BoolSort() => solver.solveOnce(boxedExpr.e.asInstanceOf[Core.Expr[Core.BoolSort]])
      case _ => failwith("c-solve-once requires boolean expression")
    }
    result match {
      case Result.SAT => Keyword.intern("sat")
      case Result.UNSAT => Keyword.intern("unsat")
      case Result.UNKNOWN => Keyword.intern("unknown")
    }
  }

  // Model extraction
  CozyFunction.cozyFunction1("model", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].solver.getModel.orNull
  }

  CozyFunction.cozyFunction1("unsat-core", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].solver.getUnsatCore.orNull
  }

  // Solver management
  CozyFunction.cozyFunction1("fork", COZY_SOLVER_NAMESPACE) { solverEnv =>
    solverEnv.asInstanceOf[SolverEnvironment].forkEnv()
  }

  CozyFunction.cozyFunction1("history", COZY_SOLVER_NAMESPACE) { solverEnv =>
    val history = solverEnv.asInstanceOf[SolverEnvironment].solver.getHistory
    RT.seq(history.asJava)
  }

  // Lowering / Lifting Operations

  CozyFunction.cozyFunction2("lower", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, expr) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val boxedExpr = expr.asInstanceOf[BoxedExpr]
    solver.lower(boxedExpr.e).asInstanceOf[AnyRef]
  }

  CozyFunction.cozyFunction2("lift", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, term) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment]
    solver.solver.liftTerm(term.asInstanceOf[solver.LoweredTerm])
  }

  CozyFunction.cozyFunction2("lift-sort", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, sort) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment]
    solver.solver.liftSort(sort.asInstanceOf[solver.solver.LoweredSort])
  }

  CozyFunction.cozyFunction2("lift-def", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, func) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment]
    solver.solver.liftFunc(func.asInstanceOf[solver.LoweredVarDecl])
  }
  
  CozyFunction.cozyFunction3("declare-var", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, name, sort) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    convert(name) match {
      case CSymbol(varName, _) =>
        val boxedSort = sort.asInstanceOf[Core.BoxedSort]
        solver.declareVar(varName, boxedSort.sort).asInstanceOf[AnyRef]

      case _ => failwith(s"Cozy error: declare-var: illegal variable name ${name}")
    }
  }

  CozyFunction.cozyFunction3("define-var", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, name, expr) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    (convert(name), CozyToFormula.cozyParseExpr(convert(expr))) match {
      case (CSymbol(varName, _), Right(parsedExpr)) => 
        val (decl, axioms) = solver.defineVar(varName, parsedExpr.sort, parsedExpr.e)
        RT.seq(decl, RT.seq(axioms.asJava))
      case _ => failwith(s"Cozy error: define var: illegal arguments ${name} and ${expr}")
    }
  }

  CozyFunction.cozyFunction2("define-sort", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, sort) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val boxedSort = sort.asInstanceOf[Core.BoxedSort]
    solver.defineSort(boxedSort.sort).asInstanceOf[AnyRef]
  }

  CozyFunction.cozyFunction2("lower-sort", COZY_SOLVER_OPS_NAMESPACE) { (solverEnv, sort) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val boxedSort = sort.asInstanceOf[Core.BoxedSort]
    solver.lowerSort(boxedSort.sort).asInstanceOf[AnyRef]
  }

  CozyFunction.cozyFunction2("init", COZY_SOLVER_NAMESPACE) { (solverEnv, logicName) =>
    val solver = solverEnv.asInstanceOf[SolverEnvironment].solver
    val logic = convert(logicName) match {
      case CKeyword("lia", _) => SmtSolver.allLia
      case CKeyword("nia", _) => SmtSolver.allNia
      case CKeyword("arith-free", _) => SmtSolver.arithFree
      case _ => failwith(s"c-initialize: unknown logic $logicName")
    }
    solver.initialize(logic)
    null
  }


  // get the parent namespace, which provides the (typeEnv, interpEnv, ?solvers) for the current namespace (if any)
  // returns a pair (CozyNamespace, Boolean) where the second parameter tells us whether
  // to clone the solvers map
  private def getParentNs(cargs: Vector[CozyExpr]): Option[(CozyNamespace, Boolean)] = {
    import CozyExpr.*
    var arg: Option[(CozyNamespace, Boolean)] = None
    cargs foreach {
      case CSeq(Vector(CKeyword("inherit", _), CSymbol(name, _), _)) =>
        arg = Some(ENV(name), false)
      case CSeq(Vector(CKeyword("inherit-all", _), CSymbol(name, _), _)) =>
        arg = Some(ENV(name), true)
      case _ => ()
    }
    arg
  }

  // Note: namespace name is quoted
  // get name of a namespace from a namespace creation command in Clojure
  private def getNsName(l: IPersistentList): (String, IPersistentStack) = {
    val nsArgs = l.pop()
    val nsname = nsArgs.peek().asInstanceOf[Symbol]
    (nsname.getName, nsArgs)
  }

  // perform creation of shadow-state variables in Cozy for corresponding Clojure
  // (create-ns ...), (ns ...) commands
  private def evalCreateNs(nsname: String, nsArgs: Vector[CozyExpr]): CozyNamespace = {
    getParentNs(nsArgs) match {
      case Some(parent, false) => // inherit typeEnv, interpEnv from parent only
        println(s"inherit from parent ${parent}")
        val cns = new CozyNamespace(Namespace.find(Symbol.intern(nsname)), parent.getTypeEnv.copy(), parent.getInterpEnv.copy())
        ENV.update(nsname, cns)
        cns
      case Some(parent, true) => // inherit typeEnv, interpEnv + solvers from parent
        println(s"inherit from parent with solver ${parent}")
        val cns = CozyNamespace(Namespace.find(Symbol.intern(nsname)), parent.getTypeEnv.copy(), parent.getInterpEnv.copy(), parent.getSolverEnvs.clone())
        ENV.update(nsname, cns)
        cns
      case None => // do not inherit from parent, roll our own shadow-state variables
        println(s"do not inherit from parent ")
        val cns = new CozyNamespace(Namespace.find(Symbol.intern(nsname)), Core.emptyTypeEnv, Core.emptyInterpEnv)
        ENV.update(nsname, cns)
        cns
    }
  }

  // proxies commands sent to the Clojure repl
  @static def eval(arg: AnyRef): AnyRef = {
    import CozyExpr.*
    val cozyArg = convert(arg)
    cozyArg match {
      case CSeq(CSymbol("quote", _) +: (sm @ CSymbol("ns" | "create-ns" | "in-ns", _)) +: CSymbol(nsName, _) +: rest) =>
        val clojureResult = EVAL.invoke(arg)
        val r = evalCreateNs(nsName, rest)
        if sm._1 == "ns" || sm._1 == "in-ns" then currentNS = r
        clojureResult
      case _ => EVAL.invoke(arg)
    }
  }

  // inspects Cozy AST and returns result to Clojure repl
  @static def inspect(e: CozyExpr): String = e.toString

  // converts a Clojure expression. covers the fragment of clojure we support.
  @static def convert(x: AnyRef): CozyExpr = {
    import CozyExpr.*
    x match {
      case null => CNil()
      case s: Symbol => CSymbol(s.getName, s.getNamespace)
      case k: Keyword => CKeyword(k.getName, namespace = k.getNamespace)
      case seq: ISeq => /* lists are ISeqs */
        val result = CSeq(iseq2vec(seq))
        result match {
          case CSeq(CSymbol("quoted", _) +: rest) => CQuoted(CSeq(rest))
          case _ => result
        }
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
  @static def revert(ex: CozyExpr): AnyRef = {
    import CozyExpr.*
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
  @static def ilist2vec(l: IPersistentList): Vector[CozyExpr] = {
    iseq2vec(l.seq())
  }

  // converts a Clojure sequence to a scala Vector
  @static def iseq2vec(seq: ISeq): Vector[CozyExpr] =
    Iterator.iterate(seq)(_.next).takeWhile(_ != null)
      .map(_.first)
      .map(convert)
      .toVector

  // ... and back
  @static def vec2iseq(vec: Vector[CozyExpr]): ISeq =
    RT.seq(vec.map(revert).asJava)

  // converts a Clojure vector into a scala Array
  @static def ivec2arr(vec: IPersistentVector): Array[CozyExpr] = {
    val len = vec.length()
    val arr = new Array[CozyExpr](len)
    (0 until len) foreach {
      idx =>
        arr(idx) = convert(vec.valAt(idx))
    }
    arr
  }

  // ... and back
  @static def arr2ivec(arr: Array[CozyExpr]): IPersistentVector =
    RT.vector(arr.map(revert) *)

  // converts a Clojure map into a Scala map
  @static def imap2map(m: IPersistentMap): Map[CozyExpr, CozyExpr] = {
    m.iterator().asScala.map {
      case e: IMapEntry => (convert(e.key()), convert(e.`val`())) // IMapEntry extends java.util.Map.Entry :contentReference[oaicite:6]{index=6}
      case e: java.util.Map.Entry[?, ?] => (convert(e.getKey), convert(e.getValue))
      case other =>
        unexpected(s"Unexpected element from IPersistentMap iterator: ${other.getClass}: $other")
    }.toMap
  }

  // ... and back
  @static def map2imap(m: Map[CozyExpr, CozyExpr]): IPersistentMap = {
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
  @static def iset2set(is: IPersistentSet): Set[CozyExpr] = {
    iseq2vec(is.seq()).map(x => convert(x)).toSet
  }

  // ... and back
  @static def set2iset(s: Set[CozyExpr]): IPersistentSet = {
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
