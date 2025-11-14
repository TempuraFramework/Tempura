package org.abstractpredicates.smt

import org.abstractpredicates.expression.Core
import org.abstractpredicates.expression.Core.FiniteUniverseSort
import org.scalatest.funsuite.AnyFunSuite
import org.abstractpredicates.expression.Syntax.*

class AllSatTests extends AnyFunSuite {

  test("allsat test 2") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv
    val z3Solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    z3Solver.initialize(SmtSolver.allLia)
    val finiteSort = typeEnv |- Core.finiteSort("U", 3)
    val funSort = Core.funSort(List(finiteSort), finiteSort)
    val funVar = interpEnv |- ("f", funSort)
    z3Solver.add(List(Core.mkEq(funVar(("x", finiteSort % 1)), (finiteSort % 2))))
    val models = z3Solver.allSat(Set(("f", funSort)))

    println(s" ******* GOT ${models.size} MODELS TOTAL **********")
    models.zipWithIndex.foreach((m, i) => println(s" model ${i}: ${m.toString}"))
  }

  test("allsat test 2b --- SmtInterpol") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val finiteSort = typeEnv |- Core.finiteSort("U", 3)
    val funSort = Core.funSort(List(finiteSort), finiteSort)
    val funVar = interpEnv |- ("f", funSort)

    val z3Solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    z3Solver.initialize(SmtSolver.allLia)
    z3Solver.add(List(Core.mkEq(funVar(("x", finiteSort % 1)), (finiteSort % 2))))
    val models = z3Solver.allSat(Set(("f", funSort)))

    println(s" ******* GOT ${models.size} MODELS TOTAL **********")
    models.zipWithIndex.foreach((m, i) => println(s" model ${i}: ${m.toString}"))
  }

  test("allsat test 2c --- CVC5") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val finiteSort = typeEnv |- Core.finiteSort("U", 3)
    val funSort = Core.funSort(List(finiteSort), finiteSort)
    val funVar = interpEnv |- ("f", funSort)

    val z3Solver = Cvc5Solver.Cvc5Solver(typeEnv, interpEnv)
    z3Solver.initialize(SmtSolver.allLia)
    z3Solver.add(List(Core.mkEq(funVar(("x", finiteSort % 1)), (finiteSort % 2))))
    val models = z3Solver.allSat(Set(("f", funSort)))

    println(s" ******* GOT ${models.size} MODELS TOTAL **********")
    models.zipWithIndex.foreach((m, i) => println(s" model ${i}: ${m.toString}"))
  }


  test("allsat test 3") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val finiteSort = typeEnv |- Core.finiteSort("U", 2)
    val funSort = Core.funSort(List(finiteSort), finiteSort)
    val funVar = interpEnv |- ("f", funSort)

    val z3Solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    z3Solver.initialize(SmtSolver.allLia)
    println(s"finite universe sort constants: ${finiteSort % 0}, ${finiteSort % 1}")

    println(s"lowered formula: ${z3Solver.lower(Core.mkEq(funVar(("x", finiteSort % 0)), (finiteSort % 0)))}")

    z3Solver.add(List(Core.mkEq(funVar(("x", finiteSort % 1)), (finiteSort % 0))))

    val models = z3Solver.allSat(Set(("f", funSort)))

    println(s" ******* GOT ${models.size} MODELS TOTAL **********")
    models.zipWithIndex.foreach((m, i) => println(s" model ${i}: ${m.toString}"))
  }

  test("allsat test 3b -- SMTInterpol") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv


    val z3Solver = SmtInterpolSolver.SmtInterpolSolver(typeEnv, interpEnv)
    z3Solver.initialize(SmtSolver.allLia)

    val finiteSort = typeEnv |- Core.finiteSort("U", 2)
    val funSort = Core.funSort(List(finiteSort), finiteSort)
    val funVar = interpEnv |- ("f", funSort)

    println(s"finite universe sort constants: ${finiteSort % 0}, ${finiteSort % 1}")

    println(s"lowered formula: ${z3Solver.lower(Core.mkEq(funVar(("x", finiteSort % 0)), (finiteSort % 0)))}")

    z3Solver.add(List(Core.mkEq(funVar(("x", finiteSort % 1)), (finiteSort % 0))))

    val models = z3Solver.allSat(Set(("f", funSort)))

    println(s" ******* GOT ${models.size} MODELS TOTAL **********")
    models.zipWithIndex.foreach((m, i) => println(s" model ${i}: ${m.toString}"))
  }


  test("allsat linear order") {
    val typeEnv = Core.emptyTypeEnv
    val interpEnv = Core.emptyInterpEnv

    val cardinality = 3

    val timeSort = typeEnv |- Core.finiteSort("time", cardinality)

    val ltSort = Core.funSort(List(timeSort.box, timeSort.box), Core.BoolSort())

    val ltDef = interpEnv |- ("lessThan", ltSort)
    val zero = interpEnv |- ("zero", timeSort)

    val solver = Z3Solver.Z3Solver(typeEnv, interpEnv)
    solver.initialize(SmtSolver.allLia)


    def app(fun: Core.Expr[Core.FunSort[Core.BoolSort]],
            args: Core.Expr[Core.FiniteUniverseSort]*): Core.Expr[Core.BoolSort] =
      val bindings = args.zipWithIndex.map { case (arg, idx) => (s"arg_$idx", arg.box()) }.toList
      Core.mkSubst("app", bindings, fun)

    def lt(lhs: Core.Expr[Core.FiniteUniverseSort], rhs: Core.Expr[Core.FiniteUniverseSort]): Core.Expr[Core.BoolSort] =
      app(ltDef, lhs, rhs)

    def vars(names: String*): List[(String, Core.BoxedSort)] =
      names.toList.map(name => (name, timeSort.box))

    def v(name: String): Core.Expr[Core.FiniteUniverseSort] =
      Core.mkVar(name, timeSort)

    // forall T, U, V.
    //  either not(T < U /\ U < V) or T < V
    val transitiveOrder =
      Core.mkForall(
        vars("T", "U", "V"),
        Core.mkNot(lt(v("T"), v("U")) /\ lt(v("U"), v("V"))) \/ lt(v("T"), v("V"))
      )

    val antisymmetric =
      Core.mkForall(
        List(("T", timeSort), ("U", timeSort)),
        Core.mkNot(lt(v("T"), v("U")) /\ lt(v("U"), v("T")))
      )

    val totalOrder =
      Core.mkForall(
        vars("T", "U"),
        lt(v("T"), v("U")) \/
          Core.mkEq(v("T"), v("U")) \/
          lt(v("U"), v("T"))
      )

    val zeroLeast =
      Core.mkForall(
        vars("X0"),
        Core.mkEq(zero, v("X0")) \/ lt(zero, v("X0"))
      )

    solver.add(List(transitiveOrder, antisymmetric, totalOrder, zeroLeast))

    val vocab: Set[(String, Core.BoxedSort)] = Set(
      ("lessThan", ltSort),
      ("zero", timeSort)
    )

    println(" *********** Starting AllSat... ********** ")
    val models = solver.allSat(vocab)
    println(s" *********** allSat done, ${models.size} total models overall ********** ")
    models.zipWithIndex.foreach((m, i) => println(s"model ${i} \n \t ${m.toString} \n"))
  }

}
