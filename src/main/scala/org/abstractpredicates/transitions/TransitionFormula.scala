package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.{Core, VariableRenamer}
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.abstraction.IdempotentSemiring
import org.abstractpredicates.transitions.TransitionFormula.Peeled.Branch
import org.abstractpredicates.smt.SmtSolver.*

object TransitionFormula {

  enum Peeled {
    case Term(t: Core.Expr[Core.BoolSort])
    case Disjunctive(args: List[Peeled])
    case Branch(premise: Core.Expr[BoolSort], conclusion: Peeled)
    case Implicative(conjuncts: List[Core.Expr[Core.BoolSort]], branches: List[Branch])

    def normalize: List[Core.Expr[Core.BoolSort]] =
      this match {
        case Term(t) => List(t)
        case Disjunctive(ts) => ts.flatMap(x => x.normalize)
        case Branch(p, c) =>
          c.normalize.map(x => Core.mkAnd(List(p, x))) // p => x
        case Implicative(List(), List(branch)) =>
          Core.mkNot(branch.premise) :: branch.normalize
        case Implicative(conjuncts, branches) =>
          branches.flatMap(
            branch => branch.normalize.map(
              y => Core.mkAnd(y :: conjuncts)))
      }
  }

  trait Peeler {
    val solverEnv: SolverEnvironment

    def peel(expr: Core.Expr[Core.BoolSort]): Peeled = {
      val solver = solverEnv.solver 
      (expr: @unchecked) match { // TODO; this is fine for now.
        case Core.Lop("or", args, BoolSort(), BoolSort()) =>
          Peeled.Disjunctive(args.map(x => peel(x)))
        case Core.Bop[BoolSort, BoolSort, BoolSort] ("=>", prem, concl, BoolSort () ) =>
          Peeled.Implicative(List(), List(Peeled.Branch(prem, peel(concl))))
        case Core.Lop("and", args, BoolSort(), BoolSort()) =>
          //
          // Pattern match on the form
          // (and <conjuncts> (=> <premise1> <concl1>) ... (=> <premise_n> <concl_n>))
          //
          // The rewrite is only sound if
          // <conjuncts> |= exactly-one(<premise1>,...,<premise_n>)
          // In other words, we check whether
          // <conjuncts> /\ (at-least-two(<premise1>,...,<premise_n>) \/ none(<premise1>,...,<premise_n>))  is UNSAT.

          val (branches, conjuncts) = // .partition: first element is ones that satisfies the predicate, second is the rest
            args.partition {
              case Core.Bop("=>", a, b, BoolSort()) =>
                true
              case _ =>
                false
            }

          val branchesP: List[Peeled.Branch] = branches map {
            case Core.Bop[BoolSort, BoolSort, BoolSort]("=>", a, b, BoolSort()) => Peeled.Branch(a, peel(b))
            case d => failwith(s"impossible ${d}")
          }

          val branchPremises = branchesP.map(x => x.premise)

          solver.push()
          val indicators: List[(Core.Expr[BoolSort], Core.Var[BoolSort])] = branchPremises.map(premise =>
            val idVar = solver.getInterp.freshVar(premise.sort)
            val id = Core.mkAnd(List(
              Core.mkImplies(idVar, premise),
              Core.mkImplies(premise, idVar)
            ))
            (id, idVar)
          )
          val query =
            Core.mkOr(List(
              Core.mkAtLeast(2, indicators.map(x => x._2)),
              Core.mkAnd(indicators.map(x => Core.mkNot(x._2)))))

          ignore(solver.add(indicators.map(x => x._1)))
          ignore(solver.add(conjuncts.map(x => x.box())))
          ignore(solver.add(List(query.box())))

          val result = solver.checkSat()
          println(s"result = ${result}")
          val returned =
            if result == Result.UNSAT then
              Peeled.Implicative(conjuncts, branchesP)
            else {
              solver.getHistory.foreach(x => println(s"history: ${x}\n"))
              println(s"model: ${solver.getModel}")
              Peeled.Term(expr)
            }
          solver.pop()
          returned
        case _ => Peeled.Term(expr)
      }
    }

  }

  object Peeler {

    def apply(solverO: SolverEnvironment)(expr: Expr[BoolSort]): Peeled = {
      new Peeler {
        override val solverEnv = solverO.solver.fork().box
      }.peel(expr)
    }
  }

  case class Transition(interpEnv: InterpEnv, typeEnv: TypeEnv, expr: Expr[BoolSort], val stateVars: Set[TimedVariable]) {

    def getExprs: Expr[BoolSort] = expr

    def renameCurrStateVariables(): Expr[BoolSort] = {
      val renameMap = scala.collection.mutable.Map[String, String]()
      stateVars.foreach(x => renameMap.update(x.getOriginalName, x.skolemized._1))
      (new VariableRenamer(renameMap.toMap)).visit(interpEnv)(expr)
    }

    def renameNextStateVariables(): Expr[BoolSort] = {
      val renameMap = scala.collection.mutable.Map[String, String]()
      stateVars.foreach(x => renameMap.update(x.getNextState, x.skolemized._1))
      (new VariableRenamer(renameMap.toMap)).visit(interpEnv)(expr)
    }
  }

  given r: IdempotentSemiring[Transition] with

    def zero: Transition = Transition(Core.emptyInterpEnv, Core.emptyTypeEnv, Core.mkFalse, Set())

    def one(interpEnv: InterpEnv, typeEnv: TypeEnv, stateVars: Set[TimedVariable]): Transition =
      Transition(interpEnv, typeEnv, Core.mkAnd(stateVars.map(x => x.identity).toList), stateVars)

    def plus(x: Transition, y: Transition): Transition = {
      if x.stateVars != y.stateVars then unsupported("cannot add transition formulas with different state variables")
      Transition(x.interpEnv ++@ y.interpEnv, x.typeEnv ++@ y.typeEnv,
        Core.mkOr(List(x.getExprs, y.getExprs)), x.stateVars)
    }

    def times(x: Transition, y: Transition): Transition = {
      if x.stateVars != y.stateVars then unsupported("cannot multiply transition formulas with different state variables")
      val boundVars = x.stateVars.toList.map(v => v.skolemized)
      Transition(x.interpEnv ++@ y.interpEnv, x.typeEnv ++@ y.typeEnv,
        Core.mkExists(boundVars, Core.mkAnd(List(x.renameNextStateVariables(), y.renameCurrStateVariables()))),
        x.stateVars)
    }

    override def one: Transition = failwith("")

}