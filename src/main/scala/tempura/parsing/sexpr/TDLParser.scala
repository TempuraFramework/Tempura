package tempura.parsing.sexpr

import tempura.expression.Core.{BoxedExpr, InterpEnv, TypeEnv, Var}
import ParseTree.*
import ParseValue.*
import tempura.expression.Syntax.*
import tempura.cozy.Transforms.*
import SmtlibParser.{parseFormula, parseSort, parseSortedArgs}
import cats.implicits.*
import tempura.helpers.Utils.*
import tempura.expression.Core
import tempura.transitions.{StateVariable, TransitionSystem, TransitionSystemBuffer}
import scala.annotation.tailrec
import scala.reflect.ClassTag

object TDLParser extends Transform[
  (Core.TypeEnv, Core.InterpEnv, List[ParseTree]), Tuple1[TransitionSystem]] {
  def parse(typeEnv: TypeEnv, interpEnv: InterpEnv)(p: TransitionSystemBuffer, tree: ParseTree): Either[String, TransitionSystemBuffer] = {
    tree match {
      case INode(List(Leaf(PTerm("state-var")), Leaf(PTerm(varName)), varSort, Leaf(PTerm(":next")), Leaf(PTerm(nextVarName)))) =>
        SmtlibParser.parseSort(typeEnv)(varSort) match {
          case Right(parsedSort) =>
            interpEnv |- (varName, parsedSort)
            interpEnv |- (nextVarName, parsedSort)
            val timedVar = StateVariable(varName, nextVarName, parsedSort)
            p.stateVars.add(timedVar)
            Right(p)
          case Left(reason) => Left(reason.toString)
        }
      case INode(List(Leaf(PTerm("transition-var")), Leaf(PTerm(varName)), varSort)) =>
        SmtlibParser.parseSort(typeEnv)(varSort) match {
          case Right(parsedSort) =>
            interpEnv |- (varName, parsedSort)
            p.transitionVars.add((varName, parsedSort))
            Right(p)
          case Left(reason) => Left(reason.toString)
        }
      case INode(List(Leaf(PTerm("var")), Leaf(PTerm(varName)), varSort)) =>
        SmtlibParser.parseSort(typeEnv)(varSort) match {
          case Right(parsedSort) =>
            interpEnv |- (varName, parsedSort)
            Right(p)
          case Left(reason) => Left(reason.toString)
        }
      case INode(List(Leaf(PTerm("var")), Leaf(PTerm(varName)), varSort, varDef)) =>
        SmtlibParser.parseSort(typeEnv)(varSort) match {
          case Right(parsedSort) =>
            SmtlibParser.parseFormula(typeEnv, interpEnv)(varDef) match {
              case Right(parsedDef) =>
                parsedSort.unifyExpr(parsedDef) match {
                  case Some(_) =>
                    interpEnv ||- (varName, parsedDef)
                    Right(p)
                  case None  => Left(s"var definition does not agree with var sort; ${parsedSort.toString} does not type-check with ${parsedDef.toString}")
                }
              case Left(reason) => Left(reason.toString)
            }
          case Left(reason) => Left(reason.toString)
        }
      case INode(List(
      Leaf(ParseValue.PTerm("fun")),
      Leaf(ParseValue.PTerm(name)),
      INode(List(
      Leaf(ParseValue.PTerm("->")),
      INode(argsSorts),
      retSort
      )))) =>
        (argsSorts.traverse(parseSort(typeEnv)), parseSort(typeEnv)(retSort)).tupled.onSuccess {
          (argSortsT, retSortT) =>
            val declareFunSort = Core.funSort(argSortsT, retSortT)
            val declareFunExpr = BoxedExpr.make(declareFunSort, Var(name, declareFunSort))
            interpEnv.add(name, declareFunExpr)
            Right(p)
        } match {
          case Right(p) => Right(p)
          case Left(e) => Left(e.toString)
        }
      case INode(List(Leaf(ParseValue.PTerm("fun")),
      Leaf(ParseValue.PTerm(name)),
      INode(List(
      INode(argsSorts),
      retSort)), body)) =>
        parseSortedArgs(typeEnv, interpEnv)(argsSorts).onSuccess { translatedSorts =>
          parseSort(typeEnv)(retSort).onSuccess { translatedRetSort =>
            parseFormula(typeEnv, interpEnv)(body).onSuccess { bodyT =>
              val domSortsT = translatedSorts.map(x => x._2)
              val funSort = Core.FunSort(domSortsT, translatedRetSort.sort)
              val funExpr = BoxedExpr.make(Core.funSort(domSortsT, bodyT.sort),
                Core.mkMacro(name, translatedSorts, bodyT.e))
              interpEnv.add(name, funExpr)
              Right(p)
            }
          }
        } match {
          case Right(p) => Right(p)
          case Left(e) => Left(e.toString)
        }
      case INode(List(Leaf(PTerm("sort")), Leaf(PTerm(varName)))) =>
        typeEnv |- Core.UnInterpretedSort(varName, 0)
        Right(p)
      case INode(List(Leaf(PTerm("finite-sort")), Leaf(PTerm(sortName)), Leaf(PNumber(size)))) =>
        typeEnv |- Core.FiniteUniverseSort(sortName, size)
        Right(p)
      case INode(List(Leaf(PTerm("vmtlib")), smtlibStmt)) =>
        VMTParser.parse(typeEnv, interpEnv)(p)(smtlibStmt) match {
          case Right(_) => Right(p)
          case Left(error) => Left(error.toString)
        }
      case INode(List(Leaf(PTerm("parameter-var")), Leaf(PTerm(varName)), sort)) =>
        SmtlibParser.parseSort(typeEnv)(sort) match {
          case Right(s) =>
            interpEnv |- (varName, s)
            Right(p)
          case Left(error) => Left(error.toString)
        }
      case INode(List(Leaf(PTerm("init")), initCond)) =>
        SmtlibParser(typeEnv, interpEnv)(initCond) match {
          case Right(fmla) =>
            fmla.unify(Core.boolSort) match {
              case Some(b) =>
                p.setInit(b)
                Right(p)
              case None =>
                Left(s"Initial condition needs to be a boolean expression, but got ${fmla.toString}")
            }
          case Left(error) => Left(error)
        }
      case INode(List(Leaf(PTerm("transition")), transitionCond)) =>
        SmtlibParser(typeEnv, interpEnv)(transitionCond) match {
          case Right(BoolExpr(fmla)) =>
            p.transitions.add(fmla)
            Right(p)
          case e => Left(s"malformed transition formula condition ($e) for: ${transitionCond}")
        }
      case INode(List(Leaf(PTerm("transition")), transitionCond, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(transitionCond) match {
          case Right(BoolExpr(fmla)) =>
            p.transitions.addNamed((fmla, name))
            Right(p)
          case e => Left(s"malformed transition formula definition ($e) for: ${tree}")

        }
      case INode(List(Leaf(PTerm("theory-axiom")), ax)) =>
        SmtlibParser(typeEnv, interpEnv)(ax) match {
          case Right(BoolExpr(fmla)) =>
            p.theoryAxioms.add(fmla)
            Right(p)
          case _ => Left(s"malformed theory axiom definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("theory-axiom")), ax, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(ax) match {
          case Right(BoolExpr(fmla)) =>
            p.theoryAxioms.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed theory axiom ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("property")), prop)) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.properties.add(fmla)
            Right(p)
          case _ => Left(s"malformed property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("property")), prop, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.properties.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed property ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("assumption")), assumed)) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.assumptions.add(fmla)
            Right(p)
          case _ => Left(s"malformed assumption definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("assumption")), assumed, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.assumptions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed assumption ${name} definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-property")), prop)) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.liveProperties.add(fmla)
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-property")), prop, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(prop) match {
          case Right(BoolExpr(fmla)) =>
            p.liveProperties.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("fair-assumption")), assumed)) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.fairnessAssumptions.add(fmla)
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("fair-assumption")), assumed, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.fairnessAssumptions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-assumption")), assumed)) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.liveAssumptions.add(fmla)
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case INode(List(Leaf(PTerm("live-assumption")), assumed, Leaf(PTerm(":name")), Leaf(PTerm(name)))) =>
        SmtlibParser(typeEnv, interpEnv)(assumed) match {
          case Right(BoolExpr(fmla)) =>
            p.liveAssumptions.addNamed((fmla, name))
            Right(p)
          case _ => Left(s"malformed liveness property definition: ${tree}")
        }
      case _ =>
        Left(s"TDLParser: unexpected input ${tree.toString}")
    }
  }

  override def apply(args: (TypeEnv, InterpEnv, List[ParseTree])): Either[String, Tuple1[TransitionSystem]] = {
    val (typeEnv, interpEnv, a) = (args._1, args._2, args._3)
    val tsBuffer = TransitionSystemBuffer()
    tsBuffer.setTypeEnv(typeEnv)
    tsBuffer.setInterpEnv(interpEnv)

    @tailrec def aux(l: List[ParseTree]): Either[String, TransitionSystemBuffer] = {
      l match {
        case a :: t =>
          parse(typeEnv, interpEnv)(tsBuffer, a) match {
            case Left(error) => Left(error)
            case Right(_) => aux(t)
          }
        case List() => Right(tsBuffer)
      }
    }

    aux(a) match {
      case Right(_) =>
        tsBuffer.toTransitionSystem match {
          case Some(ts) => Right(Tuple1(ts))
          case None => Left("error: initialization condition not set")
        }
      case Left(error) => Left(error)
    }
  }
}
