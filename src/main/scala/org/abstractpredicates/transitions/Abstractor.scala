package org.abstractpredicates.transitions

import org.abstractpredicates.expression.Core
import org.abstractpredicates.smt.SmtSolver.*
import org.abstractpredicates.transitions.TransitionFormula.Transition
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.smt.SmtSolver
import cats.syntax.all.*
import algebra.ring.Semiring
import org.abstractpredicates.smt.SmtSolver.Result.UNSAT

object Abstractor {


  class TransitionModel[LT, LVD](solver: Solver[LT, LVD],
                                 vocab: Set[TimedVariable],
                                 preStates: Set[Model[LT, LVD]], postStates: Set[Model[LT, LVD]]) {

    private val vocabPairs = vocab.map(x => (x.getOriginalName, x.getSort))

    def preStateFormula: Core.Expr[Core.BoolSort] = {
      Core.mkAnd(preStates.toList.map(x => x.formula(vocabPairs)))
    }

    def postStateImplicant: Option[Core.Expr[Core.BoolSort]] = {
      val bigFormula = postStateFormula
      def aux(imp: Set[Core.Expr[Core.BoolSort]]) : Option[Core.Expr[Core.BoolSort]] = {
        val constraint = Core.mkAnd(imp.toList)
        solver.push()
        solver.add(List(Core.mkNot(Core.mkImplies(constraint, bigFormula))))
        solver.checkSat() match {
          case UNSAT =>
            for (s <- imp.subsets(imp.size - 1)) {
              aux(s) match {
                case Some(t) =>
                  solver.pop()
                  return Some(t)
                case None => ()
              }
            }
            solver.pop()
            None
          case _ =>
            solver.pop()
            None
        }
      }
      aux(postStates.map(x => x.formula(vocabPairs)))
    }

    def postStateFormula: Core.Expr[Core.BoolSort] = {
      Core.mkAnd(postStates.toList.map(x => x.formula(vocabPairs)))
    }

    def transitionFormula: Core.Expr[Core.BoolSort] = {
      Core.mkAnd(List(preStateFormula, postStateFormula))
    }


    def relaxedTransitionFormula: Core.Expr[Core.BoolSort] = {
      Core.mkAnd(List(preStateFormula, postStateImplicant.getOrElse(postStateFormula)))
    }

    def transition: Transition = {
      Transition(solver.getInterp, solver.getTypeEnv, List(transitionFormula), vocab)
    }

    def relaxedTransition: Transition = {
      Transition(solver.getInterp, solver.getTypeEnv, List(relaxedTransitionFormula), vocab)
    }
  }

  trait AbstractorInterface {
    def performAbstraction: Transition
  }


  class DirectAbstractor[LT, LVD](solver: SmtSolver.Solver[LT, LVD], transModels: List[TransitionModel[LT, LVD]]) extends AbstractorInterface {
    override def performAbstraction: Transition = {
      transModels.map(x => x.transition).reduce(TransitionFormula.r.plus)
    }
  }

  class ImplicantAbstractor[LT, LVD](solver: SmtSolver.Solver[LT, LVD], transModels: List[TransitionModel[LT, LVD]]) extends AbstractorInterface {

    override def performAbstraction: Transition = {
      transModels.map(x =>
        x.relaxedTransition
      ).reduce(TransitionFormula.r.plus)
    }
  }


}