package org.abstractpredicates.parsing.printers

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.{InterpEnv, TypeEnv}
import org.abstractpredicates.helpers.Transforms.EnvTransform
import org.abstractpredicates.helpers.Utils.unsupported
import org.abstractpredicates.smt.SmtLibSolver
import org.abstractpredicates.transitions.TransitionSystem

import scala.collection.mutable
import scala.reflect.ClassTag

object TDLPrinter extends EnvTransform[TransitionSystem, String](using summon[ClassTag[TransitionSystem]], summon[ClassTag[String]]) {

  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(trs: TransitionSystem): Either[String, String] = {
    val smtlibPrinter = SmtLibSolver.SmtLibSolver(typeEnv, interpEnv)
    val stateOrTransitionVars: mutable.Set[String] = mutable.Set()
    // sort declarations
    val sorts = typeEnv.toList.map(x =>
      x._2.sort match {
        case Core.UnInterpretedSort(name, _) => s"(sort ${name})"
        case Core.FiniteUniverseSort(name, card) => s"(finite-sort ${name} ${card})"
        case Core.NumericSort() => "\n" // don't print out
        case Core.BoolSort() => "\n" // don't print out
        case _ => unsupported(s"TDLPrinter: cannot support printing sort ${x._2.sort.toString} yet")
      }
    ).mkString("\n")
    // state variables
    val stateVars = trs.stateVars.map(x =>
      stateOrTransitionVars.add(x.getOriginalName)
      stateOrTransitionVars.add(x.getNextState)
      s"(state-var ${x.getOriginalName} ${smtlibPrinter.lowerSort(x.getSort.sort)} :next ${x.getNextState})").mkString("\n")
    // transition variables
    val transVars = trs.transitionVars.map(x =>
      stateOrTransitionVars.add(x._1)
      s"(transition-var ${x._1} ${smtlibPrinter.lowerSort(x._2.sort)})").mkString("\n")
    // remaining variables
    val remainingVars =
      interpEnv.toList.filter(x => !stateOrTransitionVars.contains(x._1)).map(x =>
        x._2.e match {
          case Core.Var(name, fs@Core.FunSort(domSort, rangeSort)) =>
            s"(fun ${name} (-> ${domSort.map(x => smtlibPrinter.lowerSort(x)).mkString(" ")} ${smtlibPrinter.lowerSort(rangeSort)})"
          case Core.Var(name, sort) =>
            s"(state-var ${name} ${smtlibPrinter.lowerSort(sort)})"
          case Core.Macro(name, vars, body) =>
            s"(fun ${name} (-> ${vars.map(x => s"(${x._1} ${smtlibPrinter.lowerSort(x._2)})").mkString(" ")} ${smtlibPrinter.lowerSort(body.sort)}) ${smtlibPrinter.lower(body)})"
          case _ =>
            s"(var ${x._1} ${smtlibPrinter.lowerSort(x._2.sort)} ${smtlibPrinter.lower(x._2)})"
        }
      ).mkString("\n")
    // init condition
    val initCond = "(init " + smtlibPrinter.lower(trs.init) + ")"
    // transition conditions
    val transitions =
      trs.trans.map(x =>
        s"(transition ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // theory axioms
    val theoryAxioms =
      trs.theoryAxioms.map(x =>
        s"(theory-axiom ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // properties
    val properties =
      trs.properties.map(x =>
        s"(property ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // assumptions
    val assumptions =
      trs.assumptions.map(x =>
        s"(assumption ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // liveness properties
    val liveProperties =
      trs.liveProperties.map(x =>
        s"(live-property ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // live assumptions
    val liveAssumptions =
      trs.liveAssumptions.map(x =>
        s"(live-assumption ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    // fairness assumptions
    val fairAssumptions =
      trs.fairAssumptions.map(x =>
        s"(fair-assumption ${smtlibPrinter.lower(x._2)} :name ${x._1})"
      ).mkString("\n")
    inline val delim = "\n\n"
    Right(
      sorts + delim +
        stateVars + delim +
        transVars + delim +
        remainingVars + delim +
        initCond + delim +
        transitions + delim +
        theoryAxioms + delim +
        properties + delim +
        assumptions + delim +
        liveProperties + delim +
        liveAssumptions + delim +
        fairAssumptions + delim
    )
  }
}
