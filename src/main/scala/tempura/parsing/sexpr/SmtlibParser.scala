package tempura.parsing.sexpr

import ParseTree.*

import scala.::
import scala.annotation.tailrec
import scala.language.postfixOps
import scala.reflect.ClassTag
import cats.implicits.*
import tempura.cozy.Transforms.*
import tempura.transitions.*
import tempura.expression.Core
import tempura.expression.Core.*
import tempura.expression.Core.SortValue.*
import tempura.helpers.Utils.*

object SmtlibParser extends Transform[(TypeEnv, InterpEnv, ParseTree), Tuple1[Core.BoxedExpr]] {
  private def placeholderArgNames(arity: Int) = {
    (0 until arity).map(i => s"arg_$i").toList
  }

  // Translate a single sort.
  // For the leaf-level translation, we lookup a sort of name "T" in typeEnv. If T is not present
  // then returns an error. This assumes that all sort declarations have been processed and added to typeEnv.
  def parseSort(typeEnv: Core.TypeEnv)(t: ParseTree): Either[(String, ParseTree), Core.BoxedSort] = {
    t match {
      case INode(Leaf(ParseValue.PTerm("Array")) :: tail) =>
        if tail.length != 2 then
          Left("translateSort: Array length not equals 2", t)
        else
          (parseSort(typeEnv)(tail.head), parseSort(typeEnv)(tail(1))).tupled match {
            case Right(dom, range) =>
              Right(arraySort(dom.sort, range.sort))
            case _ =>
              Left(("translateSort: array malformed", t))
          }

      case INode(Leaf(ParseValue.PTerm("->")) :: tail) =>
        // XXX: we need an explicit cast here, otherwise scala compiler
        // infers tail as having a List[Any] type.
        tail.traverse(parseSort(typeEnv)) match {
          case Right(dom :+ range) =>
            Right(Core.funSort(dom, range.sort))
          case _ =>
            Left("translateSort: function sort malformed", t)
        }
      case Leaf(ParseValue.PTerm("Bool")) | INode(List(Leaf(ParseValue.PTerm("Bool")))) =>
        Right(Core.boolSort)
      case Leaf(ParseValue.PTerm("Int")) | INode(List(Leaf(ParseValue.PTerm("Int")))) =>
        Right(Core.numericSort)
      case Leaf(ParseValue.PTerm(custom)) =>
        // leaf-level translation
        typeEnv(custom) match {
          case Some(t) => Right(t)
          case None => Left(s"sort not found: $custom", t)
        }
      case INode(Leaf(ParseValue.PTerm(custom)) :: args) => // wrap every parametric sort instantiation with an AliasSort
        args.traverse(parseSort(typeEnv)) match {
          case Right(argsT) =>
            typeEnv(custom) match {
              case Some(cSort: Core.UnInterpretedSort) =>
                // We call Utils.canonicalName to come up with a canonical stringified name
                // for an instantiated parametric sort.
                Right(AliasSort(canonicalName(cSort, argsT), argsT, cSort))
              case _ =>
                Left(s"sort not found: $custom", t)
            }
          case _ =>
            Left("translateSort: parametric sort malformed", t)
        }
      case INode(List(INode(t))) => parseSort(typeEnv)(INode(t))
      case _ =>
        throw new Exception("ERROR: unhandled case: " + t.toString)

    }
  }

  // Parses arguments to an operation, where subExprs
  // is an S-expression of form INode((arg1) (arg2) ... (arg_n))
  // and each of arg_i is an Expr[X] type, and x:X is a witness for the sort X <: Sort.
  def parseOpArgs[X <: Sort[X]](typeEnv: TypeEnv, interpEnv: InterpEnv)(subExprs: List[ParseTree], x: X): Either[(String, ParseTree), List[Expr[X]]] = {
    subExprs.traverse(
      currExpr =>
        parseFormula(typeEnv, interpEnv)(currExpr) match {
          case Right(b) =>
            b.unify(x) match {
              case Some(e) => Right(e)
              case None => Left(("Cannot cast " + b.e.toString + " to type " + x.toString, currExpr))
            }
          case Left(reason) => Left(reason)
        }
    )
  }

  // Parses arguments in a function declaration of form INode((var1 Sort1) (var2 Sort2) ... (var_n Sort_n)).
  def parseSortedArgs(typeEnv: TypeEnv, interpEnv: InterpEnv)(subExprs: List[ParseTree]): Either[(String, ParseTree), List[(String, BoxedSort)]] = {
    subExprs.traverse(subExpr => subExpr match {
      case INode(List(Leaf(ParseValue.PTerm(arg)), sortExpr)) =>
        parseSort(typeEnv)(sortExpr) match {
          case Right(sort) =>
            Right(arg, sort)
          case Left(reason) =>
            Left(reason)
        }
      case _ => Left("malformed expression", subExpr)
    })
  }

  // Parses assignments to let-expressions of form (var1 expr1) (var2 expr2) ...
  // It's important ordering is guaranteed. So we can't use .traverse and need to do a foldLeft.
  def parseLetAssignment(typeEnv: TypeEnv, interpEnv: InterpEnv)(subExprs: List[ParseTree]): Either[(String, ParseTree), InterpList] = {
    subExprs.foldLeft[Either[(String, ParseTree), InterpList]](Right(List()))(
      (acc, currExpr) =>
        acc match {
          case Right(iList) =>
            currExpr match {
              case INode(List(Leaf(ParseValue.PTerm(name)), defExpr)) =>
                parseFormula(typeEnv, interpEnv)(defExpr) match {
                  case Right(defExprT) =>
                    Right((name, defExprT) :: iList)
                  case Left(reason) => Left(reason)
                }
              case _ => Left(("Mismatch in let binding", currExpr))
            }
          case Left(reason) => Left(reason)
        }
    ) match {
      case Right(t) => Right(t.reverse)
      case Left(r) => Left(r)
    }
  }

  // For a call to function f, ties up a pair (varName Sort) with a particular expression substitution.
  // Also type-checks whether the particular sub-expression is type-safe for substitution.
  def parseCallArguments(typeEnv: TypeEnv, interpEnv: InterpEnv)(argDecls: List[(String, BoxedSort)], subExprs: List[ParseTree]): Either[(String, ParseTree), InterpList] = {
    val zipped = argDecls.zip(subExprs)
    zipped.foldLeft[Either[(String, ParseTree), Core.InterpList]](Right(List()))(
      (acc, curr) =>
        (acc, parseFormula(typeEnv, interpEnv)(curr._2)) match {
          case (Right(iList), Right(currExpr)) =>
            currExpr.unify[curr._1._2.S](curr._1._2.sort) match {
              case Some(_) =>
                Right((curr._1._1, currExpr) :: iList)
              case _ =>
                Left(("parseCallArguments: Casting error", curr._2))
            }
          case (Right(_), Left(reason)) => Left(reason)
          case (Left(reason), Right(_)) => Left(reason)
          case (Left(reason1), Left(reason2)) => Left(("parseCallArguments: multiple errors: " + reason1._1 + "; " + reason2._2, curr._2))
        }
    ) match {
      case Right(iList) => Right(iList.reverse)
      case Left(r) => Left(r)
    }
  }


  // Translates an (as const ...) or (_ as (...) (...) expression
  // TODO: this is wrong
  def parseAsExpr(typeEnv: TypeEnv, interpEnv: InterpEnv)(asType: ParseTree, asTypeExpr: ParseTree): Either[(String, ParseTree), BoxedExpr] = {
    (parseFormula(typeEnv, interpEnv)(asTypeExpr), parseSort(typeEnv)(asType)) match {
      case (Right(asTypeExprT), Right(asTypeT)) =>
        asTypeExprT match {
          // the following type-test is fine, because of the semantic check in the following if-statement
          // TODO correct this type-test
          case f@FunSort(domainSort, rangeSort) =>
            asTypeExprT.unify(rangeSort) match {
              case Some(unifiedExpr) =>
                Right(BoxedExpr.make(
                  Core.funSort(domainSort, rangeSort),
                  mkMacro(getUniqueName("as-expr-macro"), List(), unifiedExpr))
                )
              case None =>
                Left(s"parseAsExpr: failed to unify ${rangeSort} with ${asTypeExprT.sort}", asTypeExpr)
            }
          case ArraySort(domSort, rangeSort) =>

            asTypeExprT.unify(rangeSort) match {
              case Some(unifiedAsTypeExpr) =>
                Right(Const(SortValue.ArrayValue(unifiedAsTypeExpr.e, ArraySort(domSort, rangeSort))))
              case None =>
                Left(s"translateAsExpr: cannot unify ${rangeSort} with ${asTypeExprT.sort}", asTypeExpr)

            }
          //  rangeSort match {
          //    case rs: asTypeExprT.T =>
          //      Right(Expr.Const(SortValue.ArrayValue(asTypeExprT.e, ArraySort(domSort, rs))))
          //  }
          //if rangeSort == asTypeExprT.sort => {
          //  Right(Expr.Const(SortValue.ArrayValue(asTypeExprT.e, ArraySort(domSort, rangeSort))))
          //}
          case _ => Left((s"translateAsExpr: cannot use as-expression to cast to ${asTypeExprT.toString}", asTypeExpr))
        }
      case (Left(reason), Right(_)) => Left(reason)
      case (Right(_), Left(reason)) => Left(reason)
      case (Left(_), Left(_)) => Left(("translateAsExpr: Malformed expression", asTypeExpr))
    }
  }

  def parseConstructor(typeEnv: TypeEnv)(t: ParseTree): Either[(String, ParseTree), Core.Constructor] = {
    t match {
      case Leaf(ParseValue.PTerm(enumConstructor)) =>
        Right(Core.Constructor(enumConstructor, List()))
      case INode(Leaf(ParseValue.PTerm(constructorName)) :: constructorArgs) =>
        constructorArgs.traverse(parseSort(typeEnv)) match {
          case Right(constructorSorts) =>
            // Seems like the SMTLIB standard does not support named arguments to constructors
            // but Z3 API does.
            Right(Constructor(constructorName, constructorSorts.zipWithIndex.map(x => (s"c_${x._2}", x._1))))
          case Left(reason) =>
            Left(reason._1, t)
        }
      case _ =>
        Left("invalid constructor declaration", t)
    }
  }

  // TODO: handling of parametricity here is a bit buggy. Need to rethink.
  @tailrec
  def parseConstructors(typeEnv: TypeEnv)(ts: List[ParseTree]): Either[(String, List[ParseTree]), List[Core.Constructor]] = {
    ts match {
      case Leaf(ParseValue.PTerm("par")) :: INode(parametricTypes) :: rest => {
        parametricTypes.traverse {
          case Leaf(ParseValue.PTerm(param)) => Some(param)
          case _ => None
        } match {
          case Some(params) =>
            parseConstructors(typeEnv ++@ (params.map(x => (x, Core.UnInterpretedSort(x, 0).box)).toEnv))(rest)
          case None =>
            Left("parametric declare-datatype statement's parameters malformed", ts)
        }
      }
      case List(Leaf(ParseValue.PTerm(constructorName))) =>
        Right(List(Core.Constructor(constructorName, List())))
      case constructorDecls =>
        constructorDecls.traverse(parseConstructor(typeEnv)) match {
          case Right(cons) => Right(cons)
          case Left(reason) => Left(reason._1, ts)
        }
    }
  }

  // translates a formula of type Expr[T], boxing the type T and the expression together in BoxedExpr.
  def parseFormula(typeEnv: TypeEnv, interpEnv: InterpEnv)(tree: ParseTree): Either[(String, ParseTree), BoxedExpr] = {
    tree match {
      case Leaf(ParseValue.PTerm(varName)) =>
        interpEnv(varName) match {
          case Some(varExpr) =>
            Right(varExpr)
          case None => Left(s"translateFormula: variable ${varName} not found in environment", tree)
        }
      case Leaf(ParseValue.PNumber(n)) =>
        Right(BoxedExpr.make(NumericSort(), Const(NumericValue(n))))
      case Leaf(ParseValue.PBool(b)) =>
        Right(BoxedExpr.make(BoolSort(), Const(BoolValue(b))))
      case Leaf(ParseValue.PString(_)) =>
        Left(("translateFormula: string types unsupported", tree))
      case INode(Leaf(ParseValue.PTerm("and")) :: subExprs) =>
        parseOpArgs[BoolSort](typeEnv, interpEnv)(subExprs, BoolSort()) match {
          case Right(args) =>
            Right(BoxedExpr.make(BoolSort(), mkLop("and", args, BoolSort(), BoolSort())))
          case Left(reason) => Left(reason)
        }
      case INode(Leaf(ParseValue.PTerm("or")) :: subExprs) =>
        parseOpArgs[BoolSort](typeEnv, interpEnv)(subExprs, BoolSort()) match {
          case Right(args) =>
            Right(BoxedExpr.make(BoolSort(), mkLop("or", args, BoolSort(), BoolSort())))
          case Left(reason) => Left(reason)
        }
      case INode(List(Leaf(ParseValue.PTerm(notTerm)), subExpr)) =>
        parseFormula(typeEnv, interpEnv)(subExpr) match {
          case Right(b) =>
            b.unify(Core.BoolSort()) match {
              case Some(bs) =>
                Right(BoxedExpr.make(BoolSort(), mkUop("not", bs, BoolSort())))
              case None => Left("translateFormula: negation only applies to bool sorted expressions", tree)
            }
          case Left(reason) => Left(reason)
        }
      case INode(List(Leaf(ParseValue.PTerm("=")), lhs, rhs)) =>
        (parseFormula(typeEnv, interpEnv)(lhs), parseFormula(typeEnv, interpEnv)(rhs)).tupled match {
          case Right(lhsT, rhsT) =>
            rhsT.unify(lhsT.sort) match {
              case Some(rhsTC) =>
                Right(BoxedExpr.make(BoolSort(), Core.mkBop("=", lhsT.e, rhsTC, BoolSort())))
              case None =>
                Left("translateFormula: cannot unify LHS and RHS types of equality symbol", tree)
            }
          case Left(reason) => Left(s"translateFormula: malformed equality comparison: ${reason._1}", tree)
        }
      case INode(List(Leaf(ParseValue.PTerm("=>")), premise, conclusion)) => // if-then
        (parseFormula(typeEnv, interpEnv)(premise), parseFormula(typeEnv, interpEnv)(conclusion)) match {
          case (Right(premiseT), Right(conclusionT)) =>
            (premiseT.unify(BoolSort()), conclusionT.unify(BoolSort())).tupled match {
              case Some(premiseB, conclusionB) =>
                Right(BoxedExpr.make(BoolSort(), Core.mkBop("=>", premiseB, conclusionB, BoolSort())))
              case None =>
                Left(s"translateFormula: implication only works on boolean formulas but got sorts ${premiseT.sort} and ${conclusionT.sort}", tree)
            }
          case (Left(reason), Right(_)) => Left(reason)
          case (Right(_), Left(reason)) => Left(reason)
          case _ => Left("translateFormula: malformed implication", tree)
        }
      case INode(List(Leaf(ParseValue.PTerm(p)), premise, thenBranch, elseBranch)) if (p == "=>" || p == "ite") => // if-then-else
        (parseFormula(typeEnv, interpEnv)(premise), parseFormula(typeEnv, interpEnv)(thenBranch), parseFormula(typeEnv, interpEnv)(elseBranch)).tupled match {
          case Right(premiseT, thenBranchT, elseBranchT) =>
            (premiseT.unify[BoolSort](BoolSort()), thenBranchT.unify(elseBranchT.sort)).tupled match {
              case Some(premiseB, thenBranchUnified) =>
                Right(
                  BoxedExpr.make(elseBranchT.sort,
                    Core.mkTop("=>", premiseB, thenBranchUnified, elseBranchT, elseBranchT.sort)
                  )
                )
              case None =>
                Left(s"translateFormula: if-then-else is ill-typed: \n premise=${premiseT} \n thenBranch=${thenBranchT} \n elseBranch=${elseBranchT}\n\n", tree)
            }
          case Left(reason) => Left(reason._1, tree)
        }
      case INode(List(Leaf(ParseValue.PTerm("forall")), INode(unparsedArgs), unparsedExpr)) =>
        parseSortedArgs(typeEnv, interpEnv)(unparsedArgs) match {
          case Right(sortedArgs) =>
            val params = sortedArgs.map(x => (x._1, BoxedExpr.make(x._2, Core.mkVar(x._1, x._2))))
            val newInterpEnv = Core.emptyInterpEnv.addFromList(params)
            parseFormula(typeEnv, interpEnv ++@ newInterpEnv)(unparsedExpr) match {
              case Right(f) =>
                f.unify[BoolSort](BoolSort()) match {
                  case Some(g) =>
                    Right(BoxedExpr.make(Core.BoolSort(), Core.mkForall(sortedArgs, g)))
                  case None =>
                    Left("translateFormula: forall works over boolean type", unparsedExpr)
                }
              case Left(reason) => Left(reason)
            }
          case Left(reason) => Left(reason)
        }
      case INode(List(Leaf(ParseValue.PTerm("exists")), INode(unparsedArgs), unparsedExpr)) =>
        parseSortedArgs(typeEnv, interpEnv)(unparsedArgs) match {
          case Right(sortedArgs) =>
            val params = sortedArgs.map(x => (x._1, BoxedExpr.make(x._2, Core.mkVar(x._1, x._2))))
            val newInterpEnv = Core.emptyInterpEnv.addFromList(params)
            parseFormula(typeEnv, interpEnv ++@ newInterpEnv)(unparsedExpr) match {
              case Right(f) =>
                f.unify[BoolSort](BoolSort()) match {
                  case Some(g) =>
                    Right(BoxedExpr.make(BoolSort(), Core.mkExists(sortedArgs, g)))
                  case None =>
                    Left("translateFormula: exists works over boolean type", unparsedExpr)
                }
              case Left(reason) => Left(reason)
            }
          case Left(reason) => Left(reason)
        }
      case INode(List(Leaf(ParseValue.PTerm("select")), arrExpr, indexExpr)) =>
        (parseFormula(typeEnv, interpEnv)(arrExpr), parseFormula(typeEnv, interpEnv)(indexExpr)).tupled match {
          case Right(arrExprT, indexExprT) =>
            arrExprT.sort match {
              case Core.ArraySort(domSort, rangeSort) =>
                // unify domain and range
                arrExprT.unify(ArraySort(indexExprT.sort, rangeSort)) match {
                  case Some(arrExprC) =>
                    Right(Core.mkSelect(arrExprC, indexExprT.e))
                  case _ =>
                    Left(s"translateFormula: failed to unify select array sort ${domSort} with ${arrExprT.sort}", tree)
                }
              case _ =>
                Left("translateFormula: select: not supplied with an array", arrExpr)
            }
          case Left(reason) => Left(s"translateFormula: malformed select statement, reason: ${reason}", tree)
        }
      case INode(List(Leaf(ParseValue.PTerm("store")), arrExpr, indexExpr, valueExpr)) =>
        (parseFormula(typeEnv, interpEnv)(arrExpr),
          parseFormula(typeEnv, interpEnv)(indexExpr),
          parseFormula(typeEnv, interpEnv)(valueExpr)).tupled match {
          case Right(arrExprT, indexExprT, valueExprT) => {
            val sort = Core.ArraySort(indexExprT.sort, valueExprT.sort)
            arrExprT.unify(sort) match {
              case Some(arrExprC) =>
                Right(BoxedExpr.make(sort,
                  Core.mkStore[indexExprT.T, valueExprT.T](
                    arrExprC,
                    indexExprT.e,
                    valueExprT.e)))
              case None =>
                Left("translateFormula: store: array expression type mismatch", arrExpr)
            }
          }
          case _ => Left("translateFormula: malformed store expression", tree)
        }
      case INode(List(Leaf(ParseValue.PTerm("let")), INode(letAssignExpr), letBody)) =>
        parseLetAssignment(typeEnv, interpEnv)(letAssignExpr) match {
          case Right(interpList) =>
            parseFormula(typeEnv, interpEnv ++@ interpList.toEnv)(letBody) match {
              case Right(letBodyT) =>
                val sortedArgs = interpList.map(x => (x._1, x._2.sort.box))
                Right(BoxedExpr.make(letBodyT.sort, //TODO: this is incorrect. Need to wrap this around with a Expr.Substitute expression.
                  Core.mkSubst("let", interpList,
                    Core.mkMacro[letBodyT.T]("letBody",
                      sortedArgs,
                      letBodyT.e
                    ))))
              case Left(reason) => Left(reason)
            }
          case Left(reason) => Left(reason)
        }
      case INode(List(INode(List(Leaf(ParseValue.PTerm("as")), Leaf(ParseValue.PTerm("const")), asConstType)), asConstExpr)) =>
        /* ((as const (Array time Bool)) true) */
        (parseFormula(typeEnv, interpEnv)(asConstExpr), parseSort(typeEnv)(asConstType)) match {
          case (Right(asConstExprT), Right(asConstTypeT)) =>
            asConstTypeT.sort match {
              case Core.ArraySort(domSort, rangeSort) =>
                asConstExprT.unify(rangeSort) match {
                  case Some(eC) =>
                    Right(Const(SortValue.ArrayValue(eC, Core.ArraySort(domSort, rangeSort))))
                  case _ => Left("translateFormula: as-const expression unification failed", tree)
                }
              case _ =>
                Left(s"translateFormula: as const expression type mismatch: expected array sort as argument but got ${asConstTypeT}", asConstType)
            }
          case (Left(reason), Right(_)) => Left(reason)
          case (Right(_), Left(reason)) => Left(reason)
          case (Left(_), Left(_)) => Left("translateFormula: malformed (as const ...) expression", tree)
        }
      case INode(List(INode(List(Leaf(ParseValue.PTerm("as")), asType)), asTypeExpr)) =>
        /* (as (Int Int) 0) */
        parseAsExpr(typeEnv, interpEnv)(asType, asTypeExpr)
      case INode(List(asTypeExpr, INode(List(Leaf(ParseValue.PTerm("as")), asType)))) =>
        /* (0 (as Int Int)) */
        parseAsExpr(typeEnv, interpEnv)(asType, asTypeExpr)
      case INode(Leaf(ParseValue.PTerm(funcCall)) :: args) =>
        // TODO: correct parsing of datatype constructor recognizers and accessors.
        // TODO | To correctly parse accessor names, we need to maintain a global table
        // TODO | of function names that are really constructor names.
        // TODO | This helps disambiguate which ones are functions and which ones are accessors.
        interpEnv(funcCall) match {
          case Some(funExpr) =>
            funExpr.e match {
              case v: Var[_] =>
                // XXX: only issue here is we
                // don't memorize the variable names of function arguments
                // for functions that are uninterpreted. This might cause issues
                // down the line, e.g., when parsing models back into environments + formulas.
                v.sort match {
                  case FunSort(domain, range) =>
                    // This is a kludge.
                    // We know that v is typed by Expr[the type of v.sort], but
                    // pattern-matching at v.sort will not help us resolve the ambiguity of v.
                    // Therefore, we need to unify again.
                    v.unify(FunSort(domain, range)) match {
                      case Some(f) =>
                        val placeholderArgs = placeholderArgNames(domain.size).zip(domain)
                        parseCallArguments(typeEnv, interpEnv)(placeholderArgs, args) match {
                          case Right(vs) =>
                            Right(BoxedExpr.make(range, Core.mkSubst("app", vs, f)))
                          case Left(reason) => Left(reason._1, tree)
                        }
                      case None => failwith("cannot happen")
                    }
                  case _ => Left(s"Cannot apply a non-function-typed variable: ${v}", tree)
                }
              case m@Macro(_, _, _) =>
                parseCallArguments(typeEnv, interpEnv)(m.vars, args) match {
                  case Right(vs) =>
                    Right(BoxedExpr.make(m.sort.rangeSort, Core.mkSubst("app", vs, m)))
                  case Left(reason) =>
                    Left(reason)
                }
              case _ =>
                Left(s"Cannot apply a non-function: ${funcCall}  boils down to ${funExpr.e} in environment", tree)
            }
          case None =>
            Left(s"function ${funcCall} not found", tree)
        }
      case INode(funAppExpr :: args) =>
        failwith(s"Cannot support arbitrary lambda-expressions yet: ${funAppExpr.toString}")
      /*val translatedBody = translateFormula(typeEnv, interpEnv)(funAppExpr)
      translatedBody match {
        case Right(funAppExprT) =>
          funAppExprT.e match {
            case v: Expr.Var[_] =>
              interpEnv(v.name) match {
                case Some(boxedF) =>
                  boxedF.e match {
                    case f @ Macro(_, _, _) =>
                      parseCallArguments(typeEnv, interpEnv)(f.vars, args) match {
                        case Right(v) =>
                          Right(BoxedExpr.make(f.sort, Core.mkSubst("app", v, f)))
                        case Left(reason) =>
                          Left(reason._1, tree)
                      }
                    case _ =>
                      Left("cannot apply a non-function", tree)
                  }
                case _ => Left("cannot find function symbol", tree)
              }
            case f: Expr.Macro[t] =>
              parseCallArguments(typeEnv, interpEnv)(f.vars, args) match {
                case Right(v) =>
                  Right(BoxedExpr.make(f.sort, Core.mkSubst("app", v, funAppExprT.e)))
                case Left(reason) => Left(reason)
              }
            case _ => Left("translateFormula: cannot apply a non-function", funAppExpr)
          }
        case Left(reason) => Left(reason)
      }*/
      case _ =>
        Left("unrecognized parse tree", tree)
    }
  }

  override def apply(args: (TypeEnv, InterpEnv, ParseTree)): Either[String, Tuple1[Core.BoxedExpr]] = {
    val (typeEnv, interpEnv, a) = (args._1, args._2, args._3)
    parseFormula(typeEnv, interpEnv)(a) match {
      case Right(parsed) => Right(Tuple1(parsed))
      case Left(error) => Left(error.toString)
    }
  }
  
  // another, more user-friendly apply
  def apply(te: TypeEnv, ie: InterpEnv)(t: ParseTree): Either[String, Core.BoxedExpr] = {
    parseFormula(te, ie)(t). match {
      case Right(parsed) => Right(parsed)
      case Left(err) => Left(err.toString)
    }
  }
  
}
