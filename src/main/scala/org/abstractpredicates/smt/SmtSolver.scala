package org.abstractpredicates.smt

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.BoxedExpr
import org.abstractpredicates.helpers.Utils.*
import scala.annotation.tailrec


// Solver-agnostic SMT interface
object SmtSolver {

  // There are three traits inside this object that an external solver implements:

  // Model - represents a model of the SMT formula
  // Solver - represents a solver
  // Translator - represents a translator between the SMT formula and the solver's internal representation

  // We also define a paired representation (Expr[X], T) for a formula in our IR and T being the translated
  // formula in a particular solver.
  type LoweredFormula[S <: Core.Sort[S], U] = (Core.Expr[S], U)

  enum LogicOption {
    case UF
    case Arithmetic
    case Quantifier
    case Datatype
    case Arrays
  }

  enum Result {
    case SAT
    case UNSAT
    case UNKNOWN

    override def toString: String =
      this match {
        case SAT => "SAT"
        case UNSAT => "UNSAT"
        case UNKNOWN => "UNKNOWN"
      }
  }

  type Logic = List[LogicOption]



  class LazyEnv[T](val lookup: String => Option[T]) {

    def apply(name: String): Option[T] = lookup(name)

    def ++@(other: LazyEnv[T]): LazyEnv[T] = {
      LazyEnv(
        (name: String) =>
          other.lookup(name) match {
            case Some(x) => Some(x)
            case None => this.lookup(name)
          }
      )
    }

  }

  trait Model[LoweredTerm, LoweredVarDecl](val solver: Solver[LoweredTerm, LoweredVarDecl]) {

    def formula(): Core.Expr[Core.BoolSort]

    def valueOf[S <: Core.Sort[S]](s: String, sort: S): Option[Core.Expr[S]]

    def vocabulary(): (List[Core.BoxedSort], List[String])

    def evaluate[S <: Core.Sort[S]](e: Core.Expr[S]): Core.BoxedExpr

    def asTerm(vocabulary: List[String]): LoweredTerm

    def asNegatedTerm(): LoweredTerm

    def asTerm(): LoweredTerm
  }
  
  trait SolverEnvironment {
    type LoweredTerm
    type LoweredVarDecl
    val solver: Solver[LoweredTerm, LoweredVarDecl]
  }
  
  extension [LT, LVD](s: Solver[LT, LVD]) {
    def box: SolverEnvironment {type LoweredTerm = LT; type LoweredVarDecl = LVD} = {
      new SolverEnvironment {
        type LoweredTerm = LT
        type LoweredVarDecl = LVD
        val solver = s
      }
    }
  }
  

  trait Solver[LT, LVD](typeEnv: Core.TypeEnv, interp: Core.InterpEnv) {

    type LoweredTerm = LT // type representing a term in underlying SMT solver
    type LoweredSort // type representing a sort in underlying SMT solver
    type LoweredVarDecl = LVD // type representing a function symbol in underlying SMT solver

    def getTypeEnv: Core.TypeEnv = {
      this.typeEnv
    }

    def getInterp: Core.InterpEnv = {
      this.interp
    }

    // There are three keywords here that are used differently.
    //  (1) "lowering" (2) "defining" and (3) "declaring."
    // A _lowering_ is an action from IR to an expression defined inside the solver that does not 
    // mutate the solver state in a visible way. For instance, a BoolSort can generally be auto-lowered
    // into the solver without mutating state (that is, introducing ancillary definitions). By contrast,
    // we _cannot_ lower an UninterpretedSort before defining or declaring it first, but such an action
    // necessarily mutates the solver state by introducing the additional sort declaration (and maybe some
    // additional axioms).
    //
    // A "defining" action is a super-set of lowering, and mostly refers to (1) user-defined sorts and
    // (2) user-defined functions. Each "definining" action introduces additional declarations into the solver
    // and also additional axioms that constrain the behavior of these declarations.
    //
    // A "declaring" action introduces declarations, but not axioms that constrain solver behavior. Essentially
    // a declared-but-undefined object is uninterpreted.

    // Compile sorts
    def lowerSort[A <: Core.Sort[A]](s: A): LoweredSort

    def defineSort[A <: Core.Sort[A]](s: A): LoweredSort

    // Compile values to constants
    def lowerValue[S <: Core.Sort[S]](sortValue: Core.SortValue[S]): LoweredTerm

    def lower[S <: Core.Sort[S]](expr: Core.Expr[S]): LoweredTerm

    def liftTerm(expr: LoweredTerm): Core.BoxedExpr

    def liftSort(sort: LoweredSort): Core.BoxedSort

    def liftFunc(func: LoweredVarDecl): Core.BoxedExpr

    def initialize(l: Logic): Unit

    def declareVar[S <: Core.Sort[S]](v: String, s: S): LoweredVarDecl

    // defineVar(v, s, e) returns a pair of (vdecl, axs) where vdecl is the declaration of the variable v
    // and axs is a possibly empty list of axioms that assert `v = e forall arguments of v`.
    def defineVar[S <: Core.Sort[S]](v: String, s: S, e: Core.Expr[S]): (LoweredVarDecl, List[LoweredTerm])

    def defineConst[S <: Core.Sort[S]](v: Core.SortValue[S]): LoweredTerm

    def add(fs: List[Core.BoxedExpr]): List[LoweredTerm]

    def addTerms(terms: List[LoweredTerm]): List[LoweredTerm]

    def push(): Unit

    def pop(): Unit

    def reset(): Unit

    // Create a new copy of solver, 
    // with fresh typeEnv and interpEnv instances
    def fork(): Solver[LT, LVD]

    def getModel: Option[Model[LT, LVD]]

    def getUnsatCore: List[LoweredTerm]

    def checkSat(): Result

    def getHistory: List[String]

    private def withPushed[T](body: => T): T =
      push()
      try body
      finally pop()

    def allSat(): List[Model[LT, LVD]] = {
      var models: List[Model[LT, LVD]] = List()

      var stop = false
      println("allSat: Starting allSat...")
      var counter = 0

      withPushed {
        while (!stop) {
          counter = counter + 1
          if checkSat() != Result.SAT then {
            stop = true
          } else getModel match {
            case Some(m) =>
              println(s"     allSat: got model ${m.toString}, round ${counter}")
              val blockingClause = m.asNegatedTerm()
              println(s"           - blocking condition: ${blockingClause.toString}")
              addTerms(List(blockingClause))
              models = m :: models
            case None =>
              stop = true
              throw new RuntimeException("checkSat reported SAT but getModel returned None")
          }
        }
      }

      models
    }
  }

}
