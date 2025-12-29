package tempura.cozy

import tempura.cozy.CS.currentNS
import tempura.expression.Core
import tempura.expression.Core.{ArraySort, BoolSort, FunSort, NumericSort}

import scala.annotation.static
import cats.implicits.*
import tempura.cozy.CS.*


trait CozyToExpr

object CozyToExpr {
  // Cozy sort -> sort
  @static def cozyParseSort(e: CExpr): Either[String, Core.BoxedSort] = {
    cozyParseSort(currentNS.getTypeEnv)(e)
  }

  private def cozyParseSort(typeEnv: Core.TypeEnv)(e: CExpr): Either[String, Core.BoxedSort] = {
    import CExpr.*
    e match {
      case CSeq(Vector(CSymbol("Array", _), arrDomExpr, arrRangeExpr)) =>

        (cozyParseSort(typeEnv)(arrDomExpr), cozyParseSort(typeEnv)(arrRangeExpr)).tupled flatMap {
          (dom, range) =>
            Right(Core.ArraySort(dom.sort, range.sort).box : Core.BoxedSort)
        }

      case (CSeq(Vector(CSymbol("->", _), CSeq(domainExprs), rangeExpr))) =>
        // Function sort: (-> D1 D2 ... Dn R) where R is the last element
        for {
          domains <- domainExprs.traverse(cozyParseSort(typeEnv))
          range <- cozyParseSort(typeEnv)(rangeExpr)
        } yield {
          val domainList = domains.foldRight(List.empty[Core.BoxedSort])((curr, acc) => curr :: acc)
          Core.funSort(domainList, range.sort)
        }
      case CSymbol("Bool", _) | CSeq(Vector(CSymbol("Bool", _))) =>
        Right(Core.boolSort)

      case CSymbol("Int", _) | CSeq(Vector(CSymbol("Int", _))) =>
        Right(Core.numericSort)

      case CSymbol(customName, _) =>
        // Look up custom sort in type environment
        typeEnv(customName) match {
          case Some(s) => Right(s)
          case None => Left(s"cozyParseSort: sort not found: $customName")
        }

      case CSeq(Vector(CSymbol(customName, _))) =>
        // Handle wrapped symbols like (CustomSort)
        typeEnv(customName) match {
          case Some(s) => Right(s)
          case None => Left(s"cozyParseSort: sort not found: $customName")
        }

      case CSeq(CSymbol(customName, _) +: args) =>
        // Parametric sort instantiation
        args.traverse(cozyParseSort(typeEnv)).flatMap { argsSorts =>
          val argList = argsSorts.foldRight(List.empty[Core.BoxedSort])((curr, acc) => curr :: acc)
          typeEnv(customName) match {
            case Some(s: Core.UnInterpretedSort) =>
              Right(Core.AliasSort(tempura.helpers.Utils.canonicalName(s,
                argList), argList, s).box)
            case Some(_) =>
              Left(s"cozyParseSort: $customName is not a parametric sort")
            case None =>
              Left(s"cozyParseSort: sort not found: $customName")
          }
        }
      case _ =>
        Left(s"cozyParseSort: unrecognized sort expression: $e")
    }
  }

  @static def cozyParseExpr(e: CExpr): Either[String, Core.BoxedExpr] = {
    cozyParseExpr(currentNS.getTypeEnv, currentNS.getInterpEnv)(e)
  }

  @static def cozyParseExpr[S <: Core.Sort[S]](e: CExpr, sort: S): Either[String, Core.Expr[S]] = {
    cozyParseExpr(e) flatMap { be =>
      be.unify(sort) match {
        case Some(e) => Right(e)
        case None => Left(s"cozyParseExpr: cannot unify ${be.sort} with ${sort}")
      }
    }
  }

  private def cozyParseExpr(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(expr: CExpr): Either[String, Core.BoxedExpr] = {
    import CExpr.*
    expr match {
      case CBool(b) =>
        Right(Core.BoxedExpr.make(BoolSort(), Core.Const(Core.SortValue.BoolValue(b))))
      case CInt(n) =>
        Right(Core.BoxedExpr.make(NumericSort(), Core.Const(Core.SortValue.NumericValue(n.toInt))))
      case CSymbol(varName, _) =>
        interpEnv(varName).toRight(s"cozyParseExpr: variable $varName not found")
      case CSeq(args) if args.isEmpty =>
        Left("cozyParseExpr: empty sequence")
      case CSeq(args) =>
        args match {
          case CSymbol("and", _) +: operands =>
            operands.traverse(cozyParseExpr(typeEnv, interpEnv)).flatMap { parsed =>
              parsed.traverse(_.unify(BoolSort()).toRight("cozyParseExpr: and requires boolean arguments"))
                .map { boolArgs =>
                  val asList = boolArgs.foldRight(List.empty[Core.Expr[BoolSort]])(_ :: _)
                  Core.BoxedExpr.make(BoolSort(), Core.mkAnd(asList))
                }
            }
          case CSymbol("or", _) +: operands =>
            operands.traverse(cozyParseExpr(typeEnv, interpEnv)).flatMap { parsed =>
              parsed.traverse(_.unify(BoolSort()).toRight("cozyParseExpr: or requires boolean arguments"))
                .map { boolArgs =>
                  val asList = boolArgs.foldRight(List.empty[Core.Expr[BoolSort]])(_ :: _)
                  Core.BoxedExpr.make(BoolSort(), Core.mkOr(asList))
                }
            }
          case Vector(CSymbol("not", _), operand) =>
            cozyParseExpr(typeEnv, interpEnv)(operand).flatMap { parsed =>
              parsed.unify(BoolSort())
                .map(b => Core.BoxedExpr.make(BoolSort(), Core.mkNot(b)))
                .toRight(s"cozyParseExpr: not requires boolean, got ${parsed.sort}")
            }
          case Vector(CSymbol("=", _), lhs, rhs) =>
            (cozyParseExpr(typeEnv, interpEnv)(lhs), cozyParseExpr(typeEnv, interpEnv)(rhs)).tupled match {
              case Right((lhsExpr, rhsExpr)) =>
                rhsExpr.unify(lhsExpr.sort)
                  .map(unified => Core.BoxedExpr.make(BoolSort(), Core.mkEq(lhsExpr.e, unified)))
                  .toRight(s"cozyParseExpr: equality sort mismatch with ${lhsExpr.sort}")
              case Left(err) => Left(err)
            }
          case CSymbol("=", _) +: _ =>
            Left("cozyParseExpr: = expects exactly two arguments")
          case Vector(CSymbol("=>", _), premise, thenBranch, elseBranch) =>
            (cozyParseExpr(typeEnv, interpEnv)(premise),
              cozyParseExpr(typeEnv, interpEnv)(thenBranch),
              cozyParseExpr(typeEnv, interpEnv)(elseBranch)).tupled match {
              case Right((condExpr, thenExpr, elseExpr)) =>
                condExpr.unify(BoolSort()) match {
                  case Some(condBool) =>
                    thenExpr.unify(elseExpr.sort) match {
                      case Some(thenUnified) =>
                        Right(Core.BoxedExpr.make(elseExpr.sort, Core.mkIte(condBool, thenUnified, elseExpr.e)))
                      case None => Left("cozyParseExpr: => branches differ")
                    }
                  case None => Left("cozyParseExpr: => premise must be boolean")
                }
              case Left(err) => Left(err)
            }
          case Vector(CSymbol("=>", _), premise, conclusion) =>
            (cozyParseExpr(typeEnv, interpEnv)(premise), cozyParseExpr(typeEnv, interpEnv)(conclusion)).tupled match {
              case Right((lhsExpr, rhsExpr)) =>
                lhsExpr.unify(BoolSort()) match {
                  case Some(lhsBool) =>
                    rhsExpr.unify(BoolSort())
                      .map(rhsBool => Core.BoxedExpr.make(BoolSort(), Core.mkImplies(lhsBool, rhsBool)))
                      .toRight("cozyParseExpr: => conclusion must be boolean")
                  case None => Left("cozyParseExpr: => premise must be boolean")
                }
              case Left(err) => Left(err)
            }
          case CSymbol("=>", _) +: _ =>
            Left("cozyParseExpr: => expects either two or three arguments")
          case Vector(CSymbol("ite", _), cond, onTrue, onFalse) =>
            (cozyParseExpr(typeEnv, interpEnv)(cond),
              cozyParseExpr(typeEnv, interpEnv)(onTrue),
              cozyParseExpr(typeEnv, interpEnv)(onFalse)).tupled match {
              case Right((condExpr, thenExpr, elseExpr)) =>
                condExpr.unify(BoolSort()) match {
                  case Some(condBool) =>
                    thenExpr.unify(elseExpr.sort) match {
                      case Some(thenUnified) =>
                        Right(Core.BoxedExpr.make(elseExpr.sort, Core.mkIte(condBool, thenUnified, elseExpr.e)))
                      case None => Left("cozyParseExpr: ite branches differ")
                    }
                  case None => Left("cozyParseExpr: ite condition must be boolean")
                }
              case Left(err) => Left(err)
            }
          case CSymbol("+", _) +: operands if operands.nonEmpty =>
            operands.traverse(cozyParseExpr(typeEnv, interpEnv)).flatMap { parsed =>
              parsed.traverse(_.unify(NumericSort()).toRight("cozyParseExpr: + requires numeric arguments"))
                .map { nums =>
                  val numList = nums.foldRight(List.empty[Core.Expr[NumericSort]])(_ :: _)
                  Core.BoxedExpr.make(NumericSort(), Core.mkAdd(numList))
                }
            }
          case CSymbol("*", _) +: operands if operands.nonEmpty =>
            operands.traverse(cozyParseExpr(typeEnv, interpEnv)).flatMap { parsed =>
              parsed.traverse(_.unify(NumericSort()).toRight("cozyParseExpr: * requires numeric arguments"))
                .map { nums =>
                  val numList = nums.foldRight(List.empty[Core.Expr[NumericSort]])(_ :: _)
                  Core.BoxedExpr.make(NumericSort(), Core.mkMul(numList))
                }
            }
          case Vector(CSymbol("-", _), operand) =>
            cozyParseExpr(typeEnv, interpEnv)(operand).flatMap { parsed =>
              parsed.unify(NumericSort())
                .map(num => Core.BoxedExpr.make(NumericSort(), Core.mkNegative(num)))
                .toRight("cozyParseExpr: unary - requires numeric argument")
            }
          case CSymbol("-", _) +: (first +: rest) if rest.nonEmpty =>
            (cozyParseExpr(typeEnv, interpEnv)(first), rest.traverse(cozyParseExpr(typeEnv, interpEnv))).tupled match {
              case Right((lhsExpr, rhsExprs)) =>
                lhsExpr.unify(NumericSort()) match {
                  case Some(lhsNum) =>
                    rhsExprs.traverse(_.unify(NumericSort()).toRight("cozyParseExpr: - requires numeric arguments")) match {
                      case Right(rhsNums) =>
                        val rhsTerm = rhsNums match {
                          case Vector(single) => single
                          case many =>
                            val rhsList = many.foldRight(List.empty[Core.Expr[NumericSort]])(_ :: _)
                            Core.mkAdd(rhsList)
                        }
                        Right(Core.BoxedExpr.make(NumericSort(), Core.mkMinus(lhsNum, rhsTerm)))
                      case Left(err) => Left(err)
                    }
                  case None => Left("cozyParseExpr: - requires numeric arguments")
                }
              case Left(err) => Left(err)
            }
          case CSymbol(op@("<" | "<=" | ">" | ">="), _) +: operands if operands.lengthCompare(1) > 0 =>
            operands.traverse(cozyParseExpr(typeEnv, interpEnv)).flatMap { parsed =>
              parsed.traverse(_.unify(NumericSort()).toRight(s"cozyParseExpr: $op requires numeric arguments")).map { nums =>
                val mkCmp: (Core.Expr[NumericSort], Core.Expr[NumericSort]) => Core.Expr[BoolSort] = op match {
                  case "<" => (a, b) => Core.mkLt(a, b)
                  case "<=" => (a, b) => Core.mkLe(a, b)
                  case ">" => (a, b) => Core.mkGt(a, b)
                  case ">=" => (a, b) => Core.mkGe(a, b)
                }
                val cmpList = nums.zip(nums.drop(1)).foldRight(List.empty[Core.Expr[BoolSort]]) {
                  case ((lhs, rhs), acc) => mkCmp(lhs, rhs) :: acc
                }
                val combined = cmpList match {
                  case Nil => Core.mkTrue
                  case single :: Nil => single
                  case many => Core.mkAnd(many)
                }
                Core.BoxedExpr.make(BoolSort(), combined)
              }
            }
          case Vector(CSymbol("select", _), arrayExpr, indexExpr) =>
            parseArraySelect(typeEnv, interpEnv)(arrayExpr, indexExpr)
          case Vector(CSymbol("store", _), arrayExpr, indexExpr, valueExpr) =>
            parseArrayStore(typeEnv, interpEnv)(arrayExpr, indexExpr, valueExpr)
          case Vector(CSymbol(q@("forall" | "exists"), _), CSeq(vars), body) =>
            vars.foldRight[Either[String, List[(String, Core.BoxedSort)]]](Right(Nil)) {
              case (CSeq(Vector(CSymbol(arg, _), sortExpr)), acc) =>
                (cozyParseSort(typeEnv)(sortExpr), acc) match {
                  case (Right(sort), Right(rest)) => Right((arg, sort) :: rest)
                  case (Left(err), _) => Left(err)
                  case (_, Left(err)) => Left(err)
                }
              case (other, _) => Left(s"cozyParseExpr: malformed binder $other")
            } match {
              case Right(sortedArgs) =>
                val bindings = sortedArgs.foldRight(List.empty[(String, Core.BoxedExpr)]) {
                  case ((name, sort), acc) =>
                    (name, Core.BoxedExpr.make(sort, Core.mkVar(name, sort))) :: acc
                }
                val scopedEnv = interpEnv ++@ Core.emptyInterpEnv.addFromList(bindings)
                cozyParseExpr(typeEnv, scopedEnv)(body).flatMap { bodyExpr =>
                  bodyExpr.unify(BoolSort()).map { boolBody =>
                    val quantified = q match {
                      case "forall" => Core.mkForall(sortedArgs, boolBody)
                      case "exists" => Core.mkExists(sortedArgs, boolBody)
                    }
                    Core.BoxedExpr.make(BoolSort(), quantified)
                  }.toRight(s"cozyParseExpr: $q body must be boolean")
                }
              case Left(err) => Left(err)
            }
          case CSymbol(func, _) +: callArgs =>
            val callList = callArgs.foldRight(List.empty[CExpr])(_ :: _)
            parseFuncCall(typeEnv, interpEnv)(func, callList)
          case _ =>
            Left(s"cozyParseExpr: unrecognized expression: $expr")
        }
      case other =>
        Left(s"cozyParseExpr: unrecognized expression: $other")
    }
  }

  private def parseArraySelect(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(arrayExpr: CExpr, indexExpr: CExpr): Either[String, Core.BoxedExpr] = {
    (cozyParseExpr(typeEnv, interpEnv)(arrayExpr), cozyParseExpr(typeEnv, interpEnv)(indexExpr)).tupled match {
      case Right((arrBoxed, idxBoxed)) =>
        arrBoxed match {
          case Core.IsArrayExpr(expr) =>
            idxBoxed.unify(expr.sort.domainSort) match {
              case Some(idxExpr) =>
                Right(Core.BoxedExpr.make(expr.sort.rangeSort, Core.mkSelect(expr, idxExpr)))
              case None => Left("cozyParseExpr: select index sort mismatch")
            }
          case _ => Left(s"cozyParseExpr: select requires array, got ${arrBoxed.sort}")
        }
      case Left(err) => Left(err)
    }
  }

  private def parseArrayStore(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(arrayExpr: CExpr, indexExpr: CExpr, valueExpr: CExpr): Either[String, Core.BoxedExpr] = {
    (cozyParseExpr(typeEnv, interpEnv)(arrayExpr),
      cozyParseExpr(typeEnv, interpEnv)(indexExpr),
      cozyParseExpr(typeEnv, interpEnv)(valueExpr)).tupled match {
      case Right((arrBoxed, idxBoxed, valBoxed)) =>
        arrBoxed match {
          case Core.IsArrayExpr(expr) =>
            idxBoxed.unify(expr.sort.domainSort) match {
              case Some(idxExpr) =>
                valBoxed.unify(expr.sort.rangeSort) match {
                  case Some(valExpr) =>
                    Right(Core.BoxedExpr.make(expr.sort, Core.mkStore(expr, idxExpr, valExpr)))
                  case None => Left("cozyParseExpr: store value sort mismatch")
                }
              case None => Left("cozyParseExpr: store index sort mismatch")
            }
          case _ => Left(s"cozyParseExpr: store requires array, got ${arrBoxed.sort}")
        }
      case Left(err) => Left(err)
    }
  }

  private def parseFuncCall(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(funcCall: String, callArgs: List[CExpr]): Either[String, Core.BoxedExpr] = {
    interpEnv(funcCall) match {
      case Some(funExpr) =>
        funExpr.e match {
          case v: Core.Var[?] =>
            v.sort match {
              case FunSort(domain, range) =>
                v.unify(FunSort(domain, range)) match {
                  case Some(f) =>
                    val placeholderArgs = placeholderArgNames(domain.size).zip(domain)
                    parseCallArguments(typeEnv, interpEnv)(placeholderArgs, callArgs).map { vs =>
                      Core.BoxedExpr.make(range, Core.mkSubst("app", vs, f))
                    }
                  case None => Left("cozyParseExpr: function unification failed")
                }
              case _ => Left(s"cozyParseExpr: cannot apply non-function: $funcCall")
            }
          case m@Core.Macro(_, _, _) =>
            parseCallArguments(typeEnv, interpEnv)(m.vars, callArgs).map { vs =>
              Core.BoxedExpr.make(m.sort.rangeSort, Core.mkSubst("app", vs, m))
            }
          case _ =>
            Left(s"cozyParseExpr: cannot apply non-function: $funcCall")
        }
      case None =>
        Left(s"cozyParseExpr: function $funcCall not found")
    }
  }

  private def placeholderArgNames(arity: Int): List[String] =
    List.tabulate(arity)(i => s"arg_$i")

  private def parseCallArguments(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)(argDecls: List[(String, Core.BoxedSort)], subExprs: List[CExpr]): Either[String, Core.InterpList] = {
    if argDecls.size != subExprs.size then
      Left(s"parseCallArguments: argument count mismatch: expected ${argDecls.size}, got ${subExprs.size}")
    else
      argDecls.zip(subExprs).traverse { case ((name, sort), expr) =>
        cozyParseExpr(typeEnv, interpEnv)(expr).flatMap { currExpr =>
          currExpr.unify(sort.sort) match {
            case Some(_) => Right((name, currExpr))
            case None => Left(s"parseCallArguments: type mismatch for argument $name")
          }
        }
      }
  }


}
