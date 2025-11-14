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

  enum Arith {
    case LIA
    case NIA
    case NoArith
  }

  // Arithmetic, Quantifier, Datatype+Arrays
  type Logic = (Arith, Boolean, Boolean)

  val arithFree: Logic = (Arith.NoArith, true, true)
  val allLia: Logic = (Arith.LIA, true, true)
  val allNia: Logic = (Arith.NIA, true, true)

  def parseLogic(l: Logic): String = {
    l match {
      case (Arith.LIA, true, true) => "AUFDTLIA"
      case (Arith.LIA, true, false) => "LIA"
      case (Arith.LIA, false, true) => "QF_AUFDTLIA"
      case (Arith.LIA, false, false) => "QF_LIA"
      case (Arith.NIA, true, true) => "AUFDTNIA"
      case (Arith.NIA, true, false) => "NIA"
      case (Arith.NIA, false, true) => "QF_AUFDTNIA"
      case (Arith.NIA, false, false) => "QF_NIA"
      case (Arith.NoArith, true, true) => "ALL"
      case (Arith.NoArith, true, false) => "AUFDTLIA"
      case (Arith.NoArith, false, true) => "QF_AUFDTLIA"
      case (Arith.NoArith, false, false) => "QF_UF"
    }
  }

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

  trait Interpretation {
    def formula(): Core.Expr[Core.BoolSort]

    def formula(vocab: Set[(String, Core.BoxedSort)]): Core.Expr[Core.BoolSort]

    def valueOf[S <: Core.Sort[S]](s: String, sort: S): Option[Core.Expr[S]]

    def vocabulary(): (List[Core.BoxedSort], List[String])

    def evaluate[S <: Core.Sort[S]](e: Core.Expr[S]): Core.Expr[S]

    def apply(arg: String, sort: Core.BoxedSort): Option[Core.BoxedExpr]
  }

  trait Model[LoweredTerm, LoweredVarDecl](val solver: Solver[LoweredTerm, LoweredVarDecl]) extends Interpretation {

    def formula(): Core.Expr[Core.BoolSort]

    def formula(vocab: Set[(String, Core.BoxedSort)]): Core.Expr[Core.BoolSort]

    def valueOf[S <: Core.Sort[S]](s: String, sort: S): Option[Core.Expr[S]]

    def vocabulary(): (List[Core.BoxedSort], List[String])

    def evaluate[S <: Core.Sort[S]](e: Core.Expr[S]): Core.Expr[S]

    def asNegatedTerm(): LoweredTerm

    def asNegatedTerm(vocab: Set[(String, Core.BoxedSort)]): LoweredTerm

    def asTerm(): LoweredTerm

    def asTerm(vocabulary: Set[(String, Core.BoxedSort)]): LoweredTerm
  }

  trait UnsatCore[LoweredTerm, LoweredVarDecl](val solver: Solver[LoweredTerm, LoweredVarDecl]) {

    def terms(): Set[LoweredTerm]

    def formulas(): Set[Core.Expr[Core.BoolSort]]
  }

  //
  // A SolverEnvironment instance is the boxed representation of a Solver instance,
  // with LoweredTerm, LoweredVarDecl both concretized
  //
  trait SolverEnvironment {
    type LoweredTerm
    type LoweredVarDecl
    val solver: Solver[LoweredTerm, LoweredVarDecl]
    
    def apply(): Solver[LoweredTerm, LoweredVarDecl] = solver
  }

  extension [LT, LVD](s: Solver[LT, LVD]) {
    def box: SolverEnvironment {type LoweredTerm = LT; type LoweredVarDecl = LVD} = {
      new SolverEnvironment {
        type LoweredTerm = LT
        type LoweredVarDecl = LVD
        val solver: Solver[LT, LVD] = s
      }
    }
  }


  //
  // Generic representation of a SMT solver interface. (LT, LVD) represents the type
  // of a formula in the backend SMT solver, and the type of a variable declaration in the
  // backend SMT solver, correspondingly. We need these information because we wish to 
  // sometimes save the work of having to re-compile formulas, as much as possible.
  //
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

    def lookupDecl[S <: Core.Sort[S]](v: String, s: S) : Option[LoweredVarDecl]
    
    def defineConst[S <: Core.Sort[S]](v: Core.SortValue[S]): LoweredTerm

    def add(fs: List[Core.BoxedExpr]): List[LoweredTerm]
    
    def addTerms(terms: List[LoweredTerm]): List[LoweredTerm]

    def addTerms(t: LoweredTerm*): List[LoweredTerm] = addTerms(t.toList)

    def push(): Unit

    def pop(): Unit

    def reset(): Unit

    // Create a new copy of solver, 
    // with fresh typeEnv and interpEnv instances
    def fork(): Solver[LT, LVD]

    def getModel: Option[Model[LT, LVD]]

    def getUnsatCore: Option[UnsatCore[LT, LVD]]

    def checkSat(): Result

    def getHistory: List[String]

    private def withPushed[T](body: => T): T =
      push()
      try body
      finally pop()

    def efficientAllSat(vocab: Set[(String, Core.BoxedSort)]): List[Model[LT, LVD]] = {
      var models: List[Model[LT, LVD]] = List()

      def aux(fixed: Map[String, LT], unfixed: List[(String, Core.BoxedSort)]) : Boolean = {
        withPushed {
          checkSat() match {
            case Result.UNSAT => false
            case Result.SAT =>
              unfixed match {
                case t :: rest =>
                  val model = getModel.get 
                  models = model :: models 
                  val tFixed = model.asTerm(Set(t))
                  val tUnfixed = model.asNegatedTerm(Set(t))
                  addTerms(tFixed)
                  aux(fixed + ((t._1, tFixed)), rest)
                  addTerms(tUnfixed)
                  aux(fixed + ((t._1, tUnfixed)), rest)
                case List() =>
                  val model = getModel.get
                  models = model :: models
                  true
              }
            case Result.UNKNOWN =>
              unexpected(s"allSat: got UNKNOWN as a result. State: \n === fixed terms === \n" +
                s"${fixed.mkString(" ;\n ")} \n === unfixed terms === \n" 
                + s"${unfixed.mkString(";\n ")}"
                + "\n === models === \n" 
                + s"${models.mkString(" ;\n ")}")
          }
        }
      }

      aux(Map(), vocab.toList)
      models
    }

    def allSat(vocab: Set[(String, Core.BoxedSort)]): List[Model[LT, LVD]] = {
      var models: List[Model[LT, LVD]] = List()

      var stop = false
      println("allSat: Starting allSat...")
      var counter = 0

      var conditions = List[LT]()
      
      withPushed {
        while (!stop) {
          counter = counter + 1
          if checkSat() != Result.SAT then {
            stop = true
          } else getModel match {
            case Some(m) =>
              println(s"     allSat: got model ${m.toString}, round ${counter}")
              val blockingClause = m.asNegatedTerm(vocab)
              println(s"=================== blocking condition: ======\n ${blockingClause.toString}\n==================")
              conditions = blockingClause :: conditions
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
