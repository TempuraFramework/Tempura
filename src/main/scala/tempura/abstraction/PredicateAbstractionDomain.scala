package tempura.abstraction

import tempura.expression.Core.ArraySort
import tempura.transitions.States.State
import tempura.expression.Syntax.*
import tempura.helpers.Utils.*
import tempura.smt.SmtSolver.SolverEnvironment

import scala.collection.mutable
import scala.language.postfixOps
import cats.implicits.*
import tempura.expression.Core
import tempura.expression.transforms.{Constants, Vocabulary}
import tempura.helpers.Utils
import tempura.parsing.printers.FormulaPrinter
import tempura.smt.{SmtSolver, Z3Solver}
import tempura.transitions.TransitionSystem

object PredicateAbstractionDomain {

  // computes the strongest formula phi such that S |= phi, described as a sum over minterms of `predicates`
  // that satisfy S
  class PredicateAbstraction(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)
                            (val states: Set[State], val predicates: List[Core.Expr[Core.BoolSort]], val vocabulary: Set[(String, Core.BoxedSort)]) {


    protected def describeStates: Core.Expr[Core.BoolSort] = {
      Core.mkAnd(states.map(x => x.getConstraint).toList)
    }

    protected def minTermFromModel[LT, LVD](mdl: SmtSolver.Model[LT, LVD],
                                            indicators: List[Core.Var[Core.BoolSort]],
                                            indicatorsToPredicates: Map[String, Core.Expr[Core.BoolSort]]): Core.Expr[Core.BoolSort] = {
      val conjunctions: List[Core.Expr[Core.BoolSort]] =
        indicators filter {
          id => mdl.evaluate(id) == Core.mkTrue
        } map {
          id => indicatorsToPredicates(id.name)
        }
      Core.mkAnd(conjunctions)
    }

    /*
      Compute the sum of minterms, each minterm being satisfied by a predicate.
     */
    def apply: Core.Expr[Core.BoolSort] = {
      val fmla = describeStates
      val indicatorToPredicates: mutable.Map[String, Core.Expr[Core.BoolSort]] = mutable.Map()
      val ie = interpEnv.copy()
      // we need a new solver for this because of the new
      // propositional variables we're adding into the solver.
      // this incurs a lot more memory if this method is called iteratively because
      // calling the Z3Solver.Z3Solver constructor creates a new Z3 context.
      val indicators = predicates.zipWithIndex.map((x, i) =>
        val id = ie |- (s"indicator_$i", Core.BoolSort())
        indicatorToPredicates.update(s"indicator_$i", x)
        id
      )
      val indicatorDefs = Core.mkAnd(indicators map {
        id => (id <=> indicatorToPredicates(id.name))
      })
      val solver = Z3Solver.Z3Solver(typeEnv, ie)
      solver.add(List(fmla /\ indicatorDefs))
      val allModels = solver.allSat(indicators.map(x => (x.name, x.sort.box)).toSet)
      val allMinTerms = allModels map { mdl => minTermFromModel(mdl, indicators, indicatorToPredicates.toMap) }
      Core.mkOr(allMinTerms)
    }
  }

  case class IndexedTemplate(args: List[(String, Core.BoxedSort)], matrix: Core.Expr[Core.BoolSort]) {
    def toExistentialFormula: Core.Expr[Core.BoolSort] = {
      args match {
        case List() => matrix
        case _ => Core.mkExists(args, matrix)
      }
    }

    def toUniversalFormula: Core.Expr[Core.BoolSort] =
      args match {
        case List() => matrix
        case _ => Core.mkForall(args, matrix)
      }

    def getMatrix: Core.Expr[Core.BoolSort] = matrix

    def getArgs: List[(String, Core.BoxedSort)] = args

    def negated: IndexedTemplate = IndexedTemplate(args, Core.mkNot(matrix))

    override def equals(obj: Any): Boolean =
      obj match {
        case IndexedTemplate(args, matrix) => args == this.args && matrix == this.matrix
        case _ => false
      }

    override def hashCode(): Int = args.hashCode() ^ matrix.hashCode()

    override def toString: String = s"IndexedTemplate(${args.mkString(", ")}) => ${FormulaPrinter(Core.emptyTypeEnv, Core.emptyInterpEnv)(matrix)}"
  }

  class IndexedPredicates(trs: TransitionSystem) {
    def getIndexSorts: Set[Core.BoxedSort] = {
      val sorts = mutable.Set[Core.BoxedSort]()
      val stateVars = trs.getStateVars
      val theoryVars = trs.getVars

      val allSorts: mutable.Set[Core.BoxedSort] = mutable.Set()
      stateVars foreach { x => allSorts.add(x.getSort) }
      theoryVars foreach { v => allSorts.add(v._2.sort.box) }

      sorts.add(Core.BoolSort()) // assume we can always quantify over BoolSort

      allSorts foreach {
        bs =>
          bs.sort match {
            case Core.ArraySort(d, _) =>
              sorts.add(d.box)
            case Core.FunSort(domain, _) =>
              domain foreach {
                domainElt => sorts.add(domainElt)
              }
            case _ => ()
          }
      }

      sorts.toSet
    }

    private def canonicalIndexName(sort: Core.BoxedSort, number: Int): String =
      "idx_" + number + "_" + sort.sort.sortName

    private def canonicalIndexName(sort: Core.BoxedSort): String = canonicalIndexName(sort, 0)

    def getIndexVariables(scheme: Set[(Core.BoxedSort, Int)]): Set[(String, Core.BoxedSort)] = {
      val indexVariables = mutable.Set[(String, Core.BoxedSort)]()
      scheme foreach {
        (bs, numVars) =>
          (0 until numVars) foreach {
            pos => indexVariables.add((canonicalIndexName(bs, pos), bs))
          }
      }
      indexVariables.toSet
    }

    def atomicPredicates(indexVars: Set[(String, Core.BoxedSort)]): List[IndexedTemplate] = {
      val atomicPredicates: mutable.Set[IndexedTemplate] = mutable.Set()
      val stateVars = trs.getStateVars map { x => (x.getOriginalName, x.getSort) }
      val theoryVars = Vocabulary(trs.getInterpEnv)(Core.mkAnd(trs.theoryAxioms.map(x => x._2)))
      val allVars = stateVars ++ theoryVars
      val sortToIndexVars: mutable.Map[Core.BoxedSort, mutable.Set[(String, Core.BoxedSort)]] = mutable.Map()

      println("ATOMIC PREDICATES: state variables = " + stateVars)
      println("ATOMIC PREDICATES: theory variables = " + theoryVars)


      indexVars foreach {
        (name, bs) =>
          sortToIndexVars.get(bs) match {
            case None => sortToIndexVars.update(bs, mutable.Set((name, bs)))
            case Some(s) => s.add((name, bs))
          }
          bs.sort match {
            case Core.BoolSort() =>
              val temp = (IndexedTemplate(List(), Core.mkVar(name, Core.BoolSort())))
              atomicPredicates.add(temp)
              atomicPredicates.add(temp.negated)
            case _ => ()
          }
      }

      // `allVars` stores symbols in the transition system that
      // might be of use to generating predicates that are R-atoms.
      allVars foreach {
        sym =>
          sym._2.sort match {
            // We add boolean symbols as an atomic predicate.
            case Core.BoolSort() =>
              atomicPredicates.add(IndexedTemplate(List(), Core.mkVar(sym._1, Core.BoolSort())))
            // An array from d -> Bool. for each index variable of sort d,
            // create an atomic predicate of form `arr[d]`.
            case Core.ArraySort(d, Core.BoolSort()) =>
              sortToIndexVars.get(d.box) match {
                case Some(s) =>
                  s foreach {
                    idx =>
                      val idxVar = Core.mkVar(idx._1, d)
                      val arr = Core.mkVar(sym._1, Core.ArraySort(d, Core.BoolSort()))
                      val atom = IndexedTemplate(List(idx), arr @< idxVar >)
                      atomicPredicates.add(atom)
                      atomicPredicates.add(atom.negated)
                  }
                case None => // might also happen if no index var is of sort d. Then we do not generate any predicates.
                  ()
              }
            // Any array of form d -> r, where r != Bool (special case covered above).
            // Treatment similar to the above.
            // That is, we figure out all index vars of sort d, and for each such var
            // we generate a predicate.
            case Core.ArraySort(d, r) =>
              (sortToIndexVars.get(d), sortToIndexVars.get(r)).tupled match {
                case Some(dSet, rSet) =>
                  dSet.zip(rSet) foreach {
                    (dIdx, rIdx) =>
                      val arr = Core.mkVar(sym._1, Core.ArraySort(d, r))
                      val dVar = Core.mkVar(dIdx._1, d)
                      val rVar = Core.mkVar(rIdx._1, r)
                      val atom = IndexedTemplate(List(dIdx, rIdx), Core.mkEq(arr @< dVar >, rVar))
                      atomicPredicates.add(atom)
                      atomicPredicates.add(atom.negated)
                  }
                case None => ()
              }
            // Function symbol of form ds[0] x ds[1] x ... ds[n] => Bool.
            case Core.FunSort(ds, Core.BoolSort()) =>
              // Make sure for each sort S that appears inside the argument list, there is at least one index variable to fill
              var feasible = true
              // check to see if there is at least 1 var per sort required
              ds foreach {
                bs =>
                  if sortToIndexVars.getOrElse(bs, mutable.Set()).isEmpty then feasible = false
              }
              val choices : mutable.ListBuffer[List[(String, Core.BoxedSort)]] = mutable.ListBuffer()
              if feasible then {
                ds foreach {
                  bs =>
                    choices.addOne(sortToIndexVars(bs).toList)
                }
                val allPossibleArgs = Utils.cartesianProduct(choices.toList)
                allPossibleArgs foreach {
                  arg =>
                    val applied = Core.mkApp(arg.map(x =>
                      val v : Core.BoxedExpr = Core.mkVar(x._1, x._2.sort).box()
                      (x._1, v)),
                      Core.mkVar(sym._1, Core.FunSort(ds, Core.BoolSort())))
                    val item = IndexedTemplate(arg, applied)
                    atomicPredicates.add(item)
                    atomicPredicates.add(item.negated)
                }
              }
            // Function symbol of form ds[0] x ds[1] x ... ds[n] => Bool.
            case Core.FunSort(ds, rangeSort) =>
              // Make sure for each sort S that appears inside the argument list, there is at least one index variable to fill
              var feasible = true
              // check to see if there is at least 1 var per sort required
              (rangeSort.box :: ds) foreach {
                bs =>
                  if sortToIndexVars.getOrElse(bs, mutable.Set()).isEmpty then feasible = false
              }
              val choices : mutable.ListBuffer[List[(String, Core.BoxedSort)]] = mutable.ListBuffer()
              if feasible then {
                ds foreach {
                  bs =>
                    choices.addOne(sortToIndexVars(bs).toList)
                }
                choices.addOne(sortToIndexVars(rangeSort.box).toList)
                val allPossibleArgs = Utils.cartesianProduct(choices.toList)
                allPossibleArgs foreach {
                  relArg =>
                    val (ret, args) = Utils.tailOfList(relArg)

                    val applied = Core.mkApp(args.map(x =>
                      val v : Core.BoxedExpr = Core.mkVar(x._1, x._2.sort).box()
                      (x._1, v)),
                      Core.mkVar(sym._1, Core.FunSort(ds, rangeSort)))
                    val expected = Core.mkVar(ret._1, rangeSort)
                    val item = IndexedTemplate(args, Core.mkEq(applied, expected))
                    atomicPredicates.add(item)
                    atomicPredicates.add(item.negated)
                }
              }
            case _ => ()
          } // end match
      }

      atomicPredicates.toList
    }
  }


  class UniversalIndexedPredicateAbstraction(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)
                                            (states: Set[State],
                                             theoryAxioms: List[Core.Expr[Core.BoolSort]],
                                             ips: List[IndexedTemplate],
                                             vocabulary: Set[(String, Core.BoxedSort)],
                                             indexVariables: Set[(String, Core.BoxedSort)])
    extends PredicateAbstraction(typeEnv, interpEnv)(states, ips.map(x => x.toUniversalFormula), vocabulary) {
    // TODO needs fix: do allsat over index variables as well
    override def apply: Core.Expr[Core.BoolSort] = {
      val fmla = this.describeStates
      val indicatorToPredicates: mutable.Map[String, Core.Expr[Core.BoolSort]] = mutable.Map()
      val ie = interpEnv.copy()
      val skolemPredicates = ips.map(x => x.getMatrix)
      val quantifierPrefix = indexVariables.toList
      // we need a new solver for this because of the new
      // propositional variables we're adding into the solver.
      // this incurs a lot more memory if this method is called iteratively because
      // calling the Z3Solver.Z3Solver constructor creates a new Z3 context.
      val indicators = skolemPredicates.zipWithIndex.map((x, i) =>
        val id = ie |- (s"indicator_$i", Core.BoolSort())
        indicatorToPredicates.update(s"indicator_$i", x)
        id
      )
      val indicatorDefs = Core.mkAnd(indicators map {
        id => (id <=> indicatorToPredicates(id.name))
      })
      val solver = Z3Solver.Z3Solver(typeEnv, ie)
      solver.add(List(Core.mkForall(quantifierPrefix, fmla /\ indicatorDefs)))
      val allModels = solver.allSat(indicators.map(x => (x.name, x.sort.box)).toSet)
      val allMinTerms = allModels map { mdl => minTermFromModel(mdl, indicators, indicatorToPredicates.toMap) }
      Core.mkOr(allMinTerms)
    }

  }


  case class ExistentialIndexedPredicateAbstraction(typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv)
                                                   (states: Set[State],
                                                    theoryAxioms: List[Core.Expr[Core.BoolSort]],
                                                    ips: List[IndexedTemplate],
                                                    vocabulary: Set[(String, Core.BoxedSort)],
                                                    indexVariables: Set[(String, Core.BoxedSort)])
    extends PredicateAbstraction(typeEnv, interpEnv)(states, ips.map(x => x.toExistentialFormula), vocabulary) {
    // TODO needs fix: do allsat over index variables as well
    override def apply: Core.Expr[Core.BoolSort] = {
      val fmla = this.describeStates
      val indicatorToPredicates: mutable.Map[String, Core.Expr[Core.BoolSort]] = mutable.Map()
      val ie = interpEnv.copy()
      val skolemPredicates = ips.map(x => x.getMatrix)
      val quantifierPrefix = indexVariables.toList
      // we need a new solver for this because of the new
      // propositional variables we're adding into the solver.
      // this incurs a lot more memory if this method is called iteratively because
      // calling the Z3Solver.Z3Solver constructor creates a new Z3 context.
      val indicators = skolemPredicates.zipWithIndex.map((x, i) =>
        val id = ie |- (s"indicator_$i", Core.BoolSort())
        indicatorToPredicates.update(s"indicator_$i", x)
        id
      )
      val indicatorDefs = Core.mkAnd(indicators map {
        id => (id <=> indicatorToPredicates(id.name))
      })
      val solver = Z3Solver.Z3Solver(typeEnv, ie)
      solver.add(List(Core.mkExists(quantifierPrefix, fmla /\ indicatorDefs)))
      val allModels = solver.allSat(indicators.map(x => (x.name, x.sort.box)).toSet ++ indexVariables)
      val allMinTerms = allModels map { mdl => minTermFromModel(mdl, indicators, indicatorToPredicates.toMap) }
      Core.mkOr(allMinTerms)
    }
  }

  case class DiagrammicAbstraction(state: State, theoryAxioms: List[Core.Expr[Core.BoolSort]]) {

    def apply: Core.Expr[Core.BoolSort] = {
      val newTerms: mutable.Map[(String, Core.BoxedSort), Core.Expr[Core.BoolSort]] = mutable.Map()
      val interpEnv = state.solverEnv.solver.getInterp
      val constants: mutable.Set[Core.BoxedSortValue] = mutable.Set()

      // map from sort -> new existential vars
      val sortToVars: mutable.Map[Core.BoxedSort, mutable.Set[String]] = mutable.Map()
      // new existential vars
      val newVars: mutable.Map[String, Core.BoxedSort] = mutable.Map()
      // equalities between state vars and existential vars
      val constToOriginalVar: mutable.Map[Core.BoxedSortValue, (String, Core.BoxedSort)] = mutable.Map()
      val quantifiedVarToOriginalVar: mutable.Map[String, (String, Core.BoxedSort)] = mutable.Map()

      // array symbols: map from arr name -> (dom, range)
      val arraySymbols: mutable.Map[String, (Core.BoxedSort, Core.BoxedSort)] = mutable.Map()
      // function symbols
      val functionSymbols: mutable.Map[String, (List[Core.BoxedSort], Core.BoxedSort)] = mutable.Map()
      // arrays from * -> bool + functions from * -> bool
      val booleanRelationSymbols: mutable.Map[String, Core.BoxedSort] = mutable.Map()

      // Below code figures out what needs to be existentially quantified.
      // Essentially, we should view functions and arrays as encoded via boolean relations
      // and avoid quantifying over them. Anything else (scalar elements) should be existentially quantified.
      state.stateVars.foreach(x =>
        val assigned = state.getAssignedStateVar(x)
        val xVar = Core.mkVar(assigned._1, assigned._2.sort)
        val xVal = state.model.evaluate(xVar)
        assigned._2.sort match {
          case Core.BoolSort() | Core.NumericSort() | Core.UnInterpretedSort(_, _) | Core.FiniteUniverseSort(_, _) =>
            val xConsts = Constants(interpEnv)(xVal)
            // this is a simplifying assumption, assuming that the RHS is really just a Const(SortValue(_)) node.
            // that is, xConsts has exactly one element.
            assert(xConsts.size == 1)
            constToOriginalVar.update(xConsts.head, (assigned._1, assigned._2.sort))
            constants ++= xConsts
          case Core.ArraySort(_, Core.BoolSort()) | Core.FunSort(_, Core.BoolSort()) =>
            booleanRelationSymbols.update(assigned._1, assigned._2)
          case Core.ArraySort(d, r) =>
            arraySymbols.update(assigned._1, (d.box, r.box))
          case Core.FunSort(ds, r) =>
            functionSymbols.update(assigned._1, (ds, r.box))
          case _ => unsupported(s"error: encountered unsupported sort: ${assigned._2.sort} in state var ${assigned._1}")
        }
      )

      // After the previous block of code, `constants` now stores all
      // constants that deserve to be replaced by existentially quantified variables.
      // Create new existential variables from constant expressions
      constants foreach {
        c =>
          val varName = Core.canonicalNameOfValue(c.value)
          val v = interpEnv |- (varName, c.value.sort)
          quantifiedVarToOriginalVar.update(varName, constToOriginalVar(c))
          sortToVars.get(c.value.sort.box) match {
            case Some(vars) => vars += Core.canonicalNameOfValue(c.value)
            case None => sortToVars.update(c.value.sort.box, mutable.Set(Core.canonicalNameOfValue(c.value)))
          }
          newVars.update(varName, c.value.sort)
      }

      /*
      For every element e_i \in D, introduce fresh variable x_{e_i}
      - phi_distinct = x_e_i \neq x_e_j
      - phi_constants = x_e_i = c for every variable c such that sigma |= c = e
      - phi_atomic = [p(x_e) = p(e)] for every choice of e such that sigma |= p(e)
      - phi_function = [f(x_e) = f(e)] for every choice of e such that sigma |= f(e)
      - phi_array = [a[x_e] = a[e]] for every choice of e such that sigma |= a[e]
       */
      // First, all existentially quantified variables of the same sort must be distinct
      val distinctFmla: Core.Expr[Core.BoolSort] = Core.mkAnd(newVars.map(
        (varName, varSort) =>
          val otherVars = sortToVars(varSort)
          val thisVar = Core.mkVar(varName, varSort)
          Core.mkAnd(otherVars.map(otherVarName =>
            val otherVar = Core.mkVar(otherVarName, varSort)
            Core.mkNot(Core.mkEq(thisVar, otherVar))).toList)
      ).toList)

      // Next, constFmla stores y = x_e for each y = e in original model.
      val constantFmla: Core.Expr[Core.BoolSort] =
        Core.mkAnd(quantifiedVarToOriginalVar.map(
          (qVarName, oVarPair) =>
            val qVar = Core.mkVar(qVarName, oVarPair._2.sort)
            val oVar = Core.mkVar(oVarPair._1, oVarPair._2.sort)
            Core.mkEq(qVar, oVar)
        ).toList)

      // Handling of array symbols.
      val arrayAtomicFmlas =
        arraySymbols map {
          (arrName, arrSort) =>
            val arrIdxs = newVars filter {
              x => x._2.sort == arrSort._1.sort
            }
            val trueIdxs = arrIdxs filter {
              x =>
                val arrDom = arrSort._1.sort
                val arrRange = arrSort._2.sort
                val arrVar = Core.mkVar(arrName, Core.ArraySort(arrDom, arrRange))
                val idxVar = Core.mkVar(x._1, arrDom)
                ??? /// TODO: need to use smt solver
            }
        }

      val atomicFmlas: Core.Expr[Core.BoolSort] = Core.mkFalse // TODO

      distinctFmla /\ constantFmla /\ atomicFmlas
    }
  }

}
