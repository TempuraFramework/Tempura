package org.abstractpredicates.parsing.sexpr

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Core.SortValue.*
import ParseTree.*
import org.abstractpredicates.helpers.Utils.*
import org.abstractpredicates.parsing.sexpr.SmtlibParser.*
import org.abstractpredicates.parsing.sexpr.SmtlibParser

import scala.::
import scala.annotation.tailrec
import scala.language.postfixOps
import scala.reflect.ClassTag
import cats.implicits.*
import org.abstractpredicates.helpers.Transforms.EnvTransform
import org.abstractpredicates.transitions.*

object VMTParser extends EnvTransform[List[ParseTree], TransitionSystem](using summon[ClassTag[List[ParseTree]]], summon[ClassTag[TransitionSystem]]) {

  @tailrec
  def parse(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(pts: PreTransitionSystem)(t: ParseTree): Either[(String, ParseTree), PreTransitionSystem] = {
    val typeEnv = pts.getTypeEnv
    val interpEnv = pts.getInterpEnv
    t match {
      case INode(List(Leaf(ParseValue.PTerm("declare-sort")), Leaf(ParseValue.PTerm(sortName)), Leaf(ParseValue.PNumber(0)))) =>
        typeEnv.add(sortName, Core.UnInterpretedSort(sortName, 0))
        Right(pts)
      case INode(List(Leaf(ParseValue.PTerm("declare-sort")), INode(List(
        Leaf(ParseValue.PTerm("!")),
        Leaf(ParseValue.PTerm(sortName)),
        Leaf(ParseValue.PTerm(":finite")),
        Leaf(ParseValue.PNumber(universeSize))
      )))) =>
        println(s"adding finite-universe sort ${sortName} of size ${universeSize}")
        typeEnv.add(sortName, Core.FiniteUniverseSort(sortName, universeSize))
        Right(pts)
      case INode(List(Leaf(ParseValue.PTerm("declare-sort")), Leaf(ParseValue.PTerm(sortName)), Leaf(ParseValue.PNumber(arity)))) =>
        typeEnv.add(sortName, Core.UnInterpretedSort(sortName, arity))
        Right(pts)
      case INode(List(Leaf(ParseValue.PTerm("declare-sort")), Leaf(ParseValue.PTerm(sortName)))) =>
        typeEnv.add(sortName, Core.UnInterpretedSort(sortName, 0))
        Right(pts)
      case INode(List(Leaf(ParseValue.PTerm("declare-datatype")), Leaf(ParseValue.PTerm(name)), INode(datatypeArgs))) =>
        parseConstructors(typeEnv)(datatypeArgs).map { constructors =>
          val nd = Core.DatatypeConstructorSort(name, constructors)
          typeEnv.add(name, nd)
          pts
        }.updateError(t)
      case INode(List(Leaf(ParseValue.PTerm("declare-const")), Leaf(ParseValue.PTerm(symbolName)), sort)) =>
        parseSort(typeEnv)(sort).map { sortT =>
          interpEnv.add(symbolName, Core.mkVar(symbolName, sortT))
          pts
        }
      case INode(List(Leaf(ParseValue.PTerm("define-const")), Leaf(ParseValue.PTerm(symbolName)), sort, expr)) =>
        (parseSort(typeEnv)(sort), parseFormula(typeEnv, interpEnv)(expr)).tupled.map { (sortT, exprT) =>
          interpEnv.add(symbolName, exprT)
          pts
        }
      // arbitrary declare-fun commands must be parsed last
      case INode(List( // state variables
      Leaf(ParseValue.PTerm("declare-fun")),
      Leaf(ParseValue.PTerm(name)),
      INode(List()),
      retSort)) =>
        parseSort(typeEnv)(retSort).map { r =>
          interpEnv.add(name, Core.BoxedExpr.make(r.sort, Var(name, r.sort)))
          pts
        }
      case INode(List( // next-state definitions
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm(_name)),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      Leaf(ParseValue.PTerm(currName)),
      Leaf(ParseValue.PTerm(":next")),
      Leaf(ParseValue.PTerm(nextName))
      ))
      )) =>
        // Next-state variables are also stored in interpEnv.
        // Instead of assigning them actual valuations, we simply treat them as
        // variables.
        parseSort(typeEnv)(retSort) match {
          case Right(r) =>
            interpEnv(nextName) match {
              case Some(expr) =>
                interpEnv.add(nextName, Core.mkVar(nextName, expr.sort))
                val stateVar = TimedVariable(currName, nextName, 0, expr.sort.box)
                pts.stateVars.add(stateVar)
                Right(pts)
              case None =>
                Left(s"next-state variable ${nextName} has no corresponding current-state ${currName} in environment", t)
            }
          case Left(reason) => Left(reason)
        }
      case INode(List( // action booleans
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm(_name)),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      Leaf(ParseValue.PTerm(actName)),
      Leaf(ParseValue.PTerm(":action")),
      Leaf(_)
      ))
      )) =>
        parseSort(typeEnv)(retSort).map(_ =>
          println(s"VMTParser: encountered action annotation ${_name}, ignoring it")
          pts
        )
      case INode(List( // initial condition
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm("init")),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      fmla,
      Leaf(ParseValue.PTerm(":init")),
      Leaf(_)
      ))
      )) =>
        println(s"***init-state formula: ${fmla.toString}")
        (parseSort(typeEnv)(retSort), parseFormula(typeEnv, interpEnv)(fmla)).tupled match {
          case Right(bs, f) if bs.sort == BoolSort() =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.setInit(bf)
                Right(pts)
              case None =>
                Left("initial condition ill-typed, not a boolean", t)
            }
          case Right(otherSort, _) =>
            Left(s"initial condition ill-typed, is ${otherSort} but not a boolean", t)
          case Left(reason) => Left(s"define-fun expression for initial condition is malformed, reason: ${reason}", t)
        }
      case INode(List( // the transition relation
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm("trans")),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      fmla,
      Leaf(ParseValue.PTerm(":trans")),
      Leaf(_)
      ))
      )) =>
        (parseSort(typeEnv)(retSort), parseFormula(typeEnv, interpEnv)(fmla)).tupled match {
          case Right(bs, f) if bs.sort == BoolSort() =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.transitions.add(bf)
                Right(pts)
              case None => Left("transition formula ill-typed, not a boolean", t)
            }
          case Right(otherSort, _) => Left(s"transition formula ill-typed: sort ${otherSort} not a boolean", t)
          case Left(reason) => Left(s"define-fun for transition formula malformed, reason: ${reason}", t)
        }
      case INode(
        List(Leaf(ParseValue.PTerm("assert")),
          INode(List(
            Leaf(ParseValue.PTerm("!")),
            fmla,
          Leaf(ParseValue.PTerm(":theory-axiom"))
          ))
      )) =>
        parseFormula(typeEnv, interpEnv)(fmla) match {
          case Right(f) =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                println(s"adding theory axiom: ${bf}")
                pts.theoryAxioms.add(bf)
                Right(pts)
              case None => Left(s"(assert ...) statement ill-typed, not a boolean but ${f.sort}", t)
            }
          case Left(reason) => Left(s"(assert (! ...)) parse error: " + reason._1, reason._2)
        }
      case INode(List( // assumptions in SMTLIB
      Leaf(ParseValue.PTerm("assert")),
      fmla
      )) =>
        parseFormula(typeEnv, interpEnv)(fmla) match {
          case Right(f) =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.properties.add(bf)
                Right(pts)
              case None => Left(s"(assert ...) statement ill-typed, not a boolean but ${f.sort}", t)
            }
          case Left(reason) => Left(s"(assert ...) parse error: " + reason._1, reason._2)
        }
      case INode(List( // liveness assumptions
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm(_name)),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      fmla,
      Leaf(ParseValue.PTerm(":react_p")),
      _
      ))
      )) =>
        (parseSort(typeEnv)(retSort), parseFormula(typeEnv, interpEnv)(fmla)).tupled match {
          case Right(bs, f) if bs.sort == BoolSort() =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.liveAssumptions.add(bf)
                Right(pts)
              case None =>
                Left(s"Liveness assumption ill-typed: ${f.sort} but not boolean", t)
            }
          case Right(sort, _) =>
            Left(s"liveness assumption ill-typed, ${sort} not a boolean", t)
          case Left(reason) => Left(s"malformed :react_p equation, reason: ${reason}", t)
        }
      case INode(List( // liveness assertions
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm(_name)),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      fmla,
      Leaf(ParseValue.PTerm(":react_q")),
      _
      ))
      )) =>
        (parseSort(typeEnv)(retSort), parseFormula(typeEnv, interpEnv)(fmla)).tupled match {
          case Right(bs, f) if bs.sort == BoolSort() =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.liveProperties.add(bf)
                Right(pts)
              case None =>
                Left(s"liveness assertion ill-typed: ${f.sort} is not a boolean", t)
            }
          case Right(sort, _) =>
            Left(s"liveness assertion ill-typed, ${sort} not a boolean", t)
          case Left(_) =>
            Left("malformed :react_q equation", t)
        }

      case INode(List( // fairness assumptions
      Leaf(ParseValue.PTerm("define-fun")),
      Leaf(ParseValue.PTerm(_name)),
      INode(List()),
      retSort,
      INode(List(
      Leaf(ParseValue.PTerm("!")),
      fmla,
      Leaf(ParseValue.PTerm(":react_r")),
      _
      ))
      )) =>
        (parseSort(typeEnv)(retSort), parseFormula(typeEnv, interpEnv)(fmla)).tupled match {
          case Right(bs, f) if bs.sort == BoolSort() =>
            f.unify(BoolSort()) match {
              case Some(bf) =>
                pts.fairnessAssumptions.add(bf)
                Right(pts)
              case None => Left(s"fairness assumption ill-typed: ${f.sort} is not boolean", t)
            }
          case Right(sort, _) =>
            Left(s"ill-typed fairness assumption: ${sort} not boolean", t)
          case Left(_) =>
            Left("malformed :react_r", t)
        }
      //
      // arbitrary function definitions and declarations, must be parsed last after all attributed declarations above.
      //
      case INode(List(
      Leaf(ParseValue.PTerm("declare-fun")),
      Leaf(ParseValue.PTerm(name)),
      INode(argsSorts),
      retSort
      )) =>
        (argsSorts.traverse(parseSort(typeEnv)), parseSort(typeEnv)(retSort)).tupled.onSuccess {
          (argSortsT, retSortT) =>
            val declareFunSort = Core.funSort(argSortsT, retSortT)
            val declareFunExpr = BoxedExpr.make(declareFunSort, Var(name, declareFunSort))
            interpEnv.add(name, declareFunExpr)
            Right(pts)
        }
      case INode(List(Leaf(ParseValue.PTerm("define-fun")), Leaf(ParseValue.PTerm(name)), INode(argsSorts), retSort, body)) =>
        parseSortedArgs(typeEnv, interpEnv)(argsSorts).onSuccess { translatedSorts =>
          parseSort(typeEnv)(retSort).onSuccess { translatedRetSort =>
            parseFormula(typeEnv, interpEnv)(body).onSuccess { bodyT =>
              val domSortsT = translatedSorts.map(x => x._2)
              val funSort = Core.FunSort(domSortsT, translatedRetSort.sort)
              val funExpr = BoxedExpr.make(Core.funSort(domSortsT, bodyT.sort),
                Core.mkMacro(name, translatedSorts, bodyT.e))
              interpEnv.add(name, funExpr)
              Right(pts)
            }
          }
        }
      case INode(List(INode(inner))) => parse(typeEnv, interpEnv)(pts)(INode(inner)) // when there are redundant nestings
      case _ =>
        Left("Error: parse(...): cannot convert AST " + t.toString, t)
    }
  }


  override def apply(typeEnv: TypeEnv, interpEnv: InterpEnv)(a: List[ParseTree]): Either[String, TransitionSystem] = {
    val pts = PreTransitionSystem()
    pts.setTypeEnv(typeEnv)
    pts.setInterpEnv(interpEnv)

    @tailrec
    def aux(s: List[ParseTree]): Either[String, PreTransitionSystem] =
      s match {
        case a :: t =>
          parse(typeEnv, interpEnv)(pts)(a) match {
            case Left(error) => Left(error.toString)
            case Right(_) => aux(t)
          }
        case List() => Right(pts)
      }

    aux(a) match {
      case Right(_) =>
        pts.toTransitionSystem match {
          case Some(t) => Right(t)
          case None => Left(s"VMTParser: required fields missing in VMT file for parsing into transition system, current state: ${pts.toString}")
        }
      case Left(reason) => Left(reason)
    }
  }
}