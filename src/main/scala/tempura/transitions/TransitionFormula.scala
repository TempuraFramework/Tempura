package tempura.transitions

import tempura.expression.Core.*
import tempura.helpers.Utils.*
import TransitionFormula.Peeled.Branch
import tempura.smt.SmtSolver.*
import tempura.expression.Syntax.*
import States.{Direction, State, StatePair}
import tempura.abstraction.IdempotentSemiring
import tempura.expression.Core
import tempura.expression.transforms.{ExprTransformer, VariableRenamer}
import tempura.parsing.printers.FormulaPrinter

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

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
      expr match { // TODO; this is fine for now.
        case Or(args) =>
          Peeled.Disjunctive(args.map(x => peel(x)))
        case Implies(prem, concl) =>
          Peeled.Implicative(List(), List(Peeled.Branch(prem, peel(concl))))
        case And(args) =>
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
            case Implies(a, b) => Peeled.Branch(a, peel(b))
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

  object TransformTransition {
    def apply(tf: Transition, transform: ExprTransformer) : Transition = {
      val typeEnv = tf.getTypeEnv
      val interpEnv = Core.TransformInterpEnv(tf.getInterpEnv, transform)
      val transitions = tf.getTransitions
      val stateVars = tf.getStateVars
      val transitionVars = tf.getTransitionVars
      val newTransitions =
        transitions map {
          (tName, expr) =>
            transform.transform(interpEnv)(expr) match {
              case BoolExpr(newExpr) =>
                (tName, newExpr)
              case e => failwith(s"TransformTransition: expected transform result to be a boolean expression, but got ${e}")
            }
        }
      Transition(interpEnv, typeEnv, newTransitions, stateVars, transitionVars)
    }
  }

  case class Transition(interpEnv: InterpEnv,
                        typeEnv: TypeEnv,
                        transitions: List[(String, Expr[BoolSort])],
                        stateVars: Set[StateVariable],
                        transitionVars: Set[(String, Core.BoxedSort)]) {

    val exprs = transitions.map(x => x._2).toArray

    val names = transitions.map(x => x._1).toArray

    def getExprs: List[Expr[BoolSort]] = exprs.toList

    def getInterpEnv: InterpEnv = interpEnv

    def getTransitions: List[(String, Expr[BoolSort])] = transitions

    def getNameOf(idx: Int): String = names(idx)

    def getTypeEnv: TypeEnv = typeEnv

    def getStateVars: Set[StateVariable] = stateVars

    def getTransitionVars: Set[(String, Core.BoxedSort)] = transitionVars

    def numTransitions: Int = exprs.length

    // for forward search, we are performing ALLSAT on next-state names because the current-state is grounded
    //  (by valuations in the current state).
    // for backward search, we perform ALLSAT on the original-state names, because the next-state is grounded
    //  (by valuations in the current state).
    private def getAllSatVocab(dir: Direction, stateVars: Set[StateVariable]): Set[(String, Core.BoxedSort)] =
      dir match {
        case States.Direction.Fwd => this.stateVars.map(x => (x.getNextState, x.getSort))
        case States.Direction.Bwd => this.stateVars.map(x => (x.getOriginalName, x.getSort))
        case States.Direction.InitFwd => this.stateVars.map(x => (x.getNextState, x.getSort))
        case States.Direction.InitBwd => this.stateVars.map(x => (x.getOriginalName, x.getSort))
      }


    private def forwardFormula(transitionIdx: Int, state: State): Expr[BoolSort] = {
      val trans = exprs(transitionIdx)
      // ground current-state variables
      val curr =
        stateVars.map(x =>
          val assigned = state.getAssignedStateVar(x)
          val v = Core.mkVar(x.getOriginalName, x.getSort.sort)
          Core.mkEq(v, state.model.valueOf(assigned._1, x.getSort.sort).get)
        )
      val eq = curr.toList match {
        case List() => Core.mkTrue
        case List(a) => a
        case l => Core.mkAnd(l)
      }
      val fmla = Core.mkAnd(List(eq, trans))
      fmla
    }

    private def backwardFormula(transitionIdx: Int, state: State): Expr[BoolSort] = {
      val trans = exprs(transitionIdx)
      // ground next-state variables
      val curr =
        stateVars.map(x =>
          val assigned = state.getAssignedStateVar(x)
          val v = Core.mkVar(x.getNextState, x.getSort.sort)
          Core.mkEq(v, state.model.valueOf(assigned._1, x.getSort.sort).get)
        )
      val eq = curr.toList match {
        case List() => Core.mkTrue
        case List(a) => a
        case l => Core.mkAnd(l)
      }
      val fmla = Core.mkAnd(List(eq, trans))
      fmla

    }

    // one state from a particular transition
    private def oneState(f: (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Option[(StatePair, State)] = {
      val solver = solverEnv.solver
      val fmla = f(transitionIdx, state)
      solver.push()
      solver.add(List(fmla))
      val result = solver.checkSat() match {
        case Result.SAT =>
          Some(States.StatePair(transitionVars, solverEnv, solver.getModel.get), States.State(stateVars, solverEnv, solver.getModel.get, dir))
        case _ => None
      }
      solver.pop()
      result
    }

    def oneForwardState(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Option[(StatePair, State)] =
      oneState(forwardFormula, States.Direction.Fwd)(solverEnv, state, transitionIdx)

    def oneBackwardState(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Option[(StatePair, State)] =
      oneState(backwardFormula, States.Direction.Bwd)(solverEnv, state, transitionIdx)

    // one state from any transition
    private def oneState(f: (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State): Option[(Int, StatePair, State)] = {
      val worklist = mutable.Queue[Int]()
      exprs.indices foreach { x => worklist.enqueue(x) }
      var result: Option[(Int, StatePair, State)] = None
      while (worklist.nonEmpty && result.isEmpty) {
        val exprIdx = worklist.dequeue()
        oneState(f, dir)(solverEnv, state, exprIdx) match {
          case Some(s) => result = Some(exprIdx, s._1, s._2)
          case None => ()
        }
      }
      result
    }

    def oneForwardState(solverEnv: SolverEnvironment, state: State): Option[(Int, StatePair, State)] =
      oneState(forwardFormula, States.Direction.Fwd)(solverEnv, state)

    def oneBackwardState(solverEnv: SolverEnvironment, state: State): Option[(Int, StatePair, State)] =
      oneState(backwardFormula, States.Direction.Bwd)(solverEnv, state)

    // set of states of size n from a particular transition
    private def states(f : (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State, transitionIdx: Int, n: Int): Set[(StatePair, State)] = {
      val fmla = f(transitionIdx, state)
      val solver = solverEnv.solver
      solver.push()
      solver.add(List(fmla))
      val allSatVocab = getAllSatVocab(dir, state.stateVars)
      val result = solver.partialAllSat(allSatVocab, n).map(
        model => (StatePair(this.transitionVars, solverEnv, model), State(this.stateVars, solverEnv, model, dir))
      ).toSet
      solver.pop()
      result
    }

    def forwardStates(solverEnv: SolverEnvironment, state: State, transitionIdx: Int, n: Int): Set[(StatePair, State)] =
      states(forwardFormula, States.Direction.Fwd)(solverEnv, state, transitionIdx, n)

    def backwardStates(solverEnv: SolverEnvironment, state: State, transitionIdx: Int, n: Int): Set[(StatePair, State)] =
      states(backwardFormula, States.Direction.Bwd)(solverEnv, state, transitionIdx, n)

    // set of forward states from any transition
    private def states(f : (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State, n: Int): Set[(StatePair, State)] = {
      var idx = 0
      val s : mutable.Set[(StatePair, State)] = mutable.Set()
      while (idx < this.numTransitions && s.size < n) {
        s ++= states(f, dir)(solverEnv, state, idx, n)
        idx = idx + 1
      }
      s.toSet
    }

    def forwardStates(solverEnv: SolverEnvironment, state: State, n: Int) : Set[(StatePair, State)] =
      states(forwardFormula, States.Direction.Fwd)(solverEnv, state, n)
    
    def backwardStates(solverEnv: SolverEnvironment, state: State, n: Int) : Set[(StatePair, State)] =
      states(backwardFormula, States.Direction.Bwd)(solverEnv, state, n)
    
    // set of all states from a particular transition
    private def allStates(f: (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Set[(StatePair, State)] = {
      val fmla = f(transitionIdx, state)
      println(s"allStates: formula = ${FormulaPrinter(typeEnv, interpEnv)(fmla)}")
      val solver = solverEnv.solver
      solver.push()
      solver.add(List(fmla))
      println(s"allStates: state variables ${this.stateVars.map(x => s"${x.getOriginalName} : ${x.getSort.sort}").mkString(", ")}")

      val allSatVocab = getAllSatVocab(dir, state.stateVars)

      val result = solver.allSat(allSatVocab)
        .map(model =>
          println(s"  allStates: model = ${model}")
          (StatePair(this.transitionVars, solverEnv, model), State(this.stateVars, solverEnv, model, dir))).toSet
      solver.pop()
      result
    }
    
    def forwardAllStates(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Set[(StatePair, State)] =
      allStates(forwardFormula, States.Direction.Fwd)(solverEnv, state, transitionIdx)


    def backwardAllStates(solverEnv: SolverEnvironment, state: State, transitionIdx: Int): Set[(StatePair, State)] =
      allStates(backwardFormula, States.Direction.Bwd)(solverEnv, state, transitionIdx)
    
    // set of all forward states from all transitions
    private def allStates(f: (Int, State) => Expr[BoolSort], dir: States.Direction)(solverEnv: SolverEnvironment, state: State): List[Set[(StatePair, State)]] = {
      val as : mutable.ListBuffer[Set[(StatePair, State)]] = ListBuffer()
      (0 until this.numTransitions) foreach {
        idx =>
          as += allStates(f, dir)(solverEnv, state, idx)
      }
      as.toList
    }

    def forwardAllStates(solverEnv: SolverEnvironment, state: State): List[Set[(StatePair, State)]] =
      allStates(forwardFormula, States.Direction.Fwd)(solverEnv, state)


    def backwardAllStates(solverEnv: SolverEnvironment, state: State): List[Set[(StatePair, State)]] =
      allStates(backwardFormula, States.Direction.Bwd)(solverEnv, state)

  }
}