package tempura.expression.transforms

import tempura.expression.Core.*
import tempura.helpers.Utils.*

import cats.implicits.*
import tempura.expression.Core

class SortRenamer(renamedSorts: Map[String, BoxedSort]) extends ExprTransformer {

  override def varTransformer[A <: Core.Sort[A]](env: InterpEnv)(v: Var[A]): Core.BoxedExpr = {

    v.sort match {
      case UnInterpretedSort(name, _) =>
        renamedSorts.get(v.sort.sortName) match {
          case Some(newSort: BoxedSort) =>
            Var(v.name, newSort)
          case _ => v
        }
      case ArraySort(d, r) =>
        (renamedSorts.get(d.sortName), renamedSorts.get(r.sortName)) match {
          case (Some(dSort: BoxedSort), Some(rSort: BoxedSort)) =>
            Var(v.name, ArraySort(dSort, rSort))
          case (Some(dSort), None) =>
            Var(v.name, ArraySort(dSort, r))
          case (None, Some(rSort)) =>
            Var(v.name, ArraySort(d, rSort))
          case _ =>
            Var(v.name, ArraySort(d, r))
        }
      case FunSort(domain, rangeSort) =>
        val newDomain: List[BoxedSort] = domain.map(x =>
          renamedSorts.get(x.sort.sortName) match {
            case Some(newSort) => newSort
            case None => x
          }
        )
        val newRange: BoxedSort = renamedSorts.get(rangeSort.sortName) match {
          case Some(newSort) => newSort
          case None => rangeSort.box
        }
        Var(v.name, FunSort(newDomain, newRange.sort))
      case NumericSort() => Var(v.name, NumericSort())
      case BoolSort() => Var(v.name, BoolSort())
      case FiniteUniverseSort(_, _) => v
      case DatatypeConstructorSort(_, _) => v
      case AliasSort(_, _, _) => v
    }
  }

  override def forallTransformer(env: InterpEnv)(expr: Forall): BoxedExpr = {
    val args = expr.vars.map(x =>
      renamedSorts.get(x._2.sort.sortName) match {
        case Some(newSort: BoxedSort) => (x._1, newSort)
        case None => x
      })
    val body = transform(env)(expr.body)

    body.unify(Core.BoolSort()) match {
      case Some(bExpr) => Forall(args, bExpr)
      case None => failwith(s"forallTransformer: forall body transformed into a non-boolean expression: ${body}")
    }
  }

  override def existsTransformer(env: InterpEnv)(expr: Exists): BoxedExpr = {
    val args = expr.vars.map(x =>
      renamedSorts.get(x._2.sort.sortName) match {
        case Some(newSort: BoxedSort) => (x._1, newSort)
        case None => x
      })
    val body = transform(env)(expr.body)

    body.unify(Core.BoolSort()) match {
      case Some(bExpr) => Exists(args, bExpr)
      case None => failwith(s"forallTransformer: forall body transformed into a non-boolean expression: ${body}")
    }
  }

  override def macroTransformer[X <: Sort[X]](env: InterpEnv)(expr: Macro[X]): BoxedExpr = {
    val args = expr.vars.map(x =>
      renamedSorts.get(x._2.sort.sortName) match {
        case Some(newSort: BoxedSort) => (x._1, newSort)
        case None => x
      }
    )
    val body = transform(env)(expr.expr)
    val argSorts = args.map(_._2)
    val bodySort = body.sort
    Macro(expr.name, args, body)(using Core.funSort(argSorts, bodySort))
  }

  override def substituteTransformer[X <: Sort[X]](env: InterpEnv)(expr: Substitute[X]): BoxedExpr = {
    val transformedArgs =
      expr.varBindings.map(x =>
        (x._1, transform(env)(x._2))
      )
    // XXX: probably shouldn't beta-reduce here  
    // val newEnv = env ++@ transformedArgs.toEnv
    val body = transform(env)(expr.expr)
    body.unbox match {
      case m@Macro(newName, newArgs, newBody) =>
        Substitute(expr.attribute, transformedArgs, m)(using m.sort)
      case v@Var(name, f@Core.FunSort(dom, range)) =>
        Substitute(expr.attribute, transformedArgs, Var(name, f))(using f)
      case _ =>
        body
    }
  }

  // TODO
  override def arraySelectTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArraySelect[X, Y]): BoxedExpr = {
    val arrExpr = a.a
    val arrSelectorExpr = a.index
    val arrT = transform(env)(arrExpr)
    val arrSelectorT = transform(env)(arrSelectorExpr)

    arrT.sort match {
      case ArraySort(d, r) =>
        // XXX: this is a kludge. technically arrT is typed by ArrT.sort, but
        // since scala doesn't have flow-sensitive typing there's no way to typecheck this
        // unless we re-unify arrT.e with arrT.sort once arrT.sort resolves to a particular type.
        (arrT.unify(ArraySort(d, r)), arrSelectorT.unify(d)).tupled match {
          case Some(arrU, arrSelectorU) =>
            Core.mkSelect(arrU, arrSelectorU)
          case _ => failwith("")
        }
      case _ => failwith("")
    }
  }

  override def arrayStoreTransformer[X <: Sort[X], Y <: Sort[Y]](env: InterpEnv)(a: ArrayStore[X, Y]): BoxedExpr = {
    val arrExpr = a.a
    val arrSelectExpr = a.index
    val arrStoreExpr = a.value
    val arrT = transform(env)(arrExpr)
    val arrSelectT = transform(env)(arrSelectExpr)
    val arrStoreT = transform(env)(arrStoreExpr)
    arrT.sort match {
      case ArraySort(d, r) =>
        (arrT.unify(ArraySort(d, r)), arrSelectT.unify(d), arrStoreT.unify(r)).tupled match {
          case Some(arrU, arrSelectU, arrStoreU) =>
            Core.mkStore(arrU, arrSelectU, arrStoreU)
          case _ => failwith("")
        }
      case _ => failwith("")
    }
  }


  // TODO: how to handle uninterpreted constants? ---> Need to impose some sort of ordering over universe elements.
  override def constTransformer[A <: Core.Sort[A]](env: InterpEnv)(v: Const[A]): Core.BoxedExpr = {
    v.sortValue match {
      case u: Core.SortValue.UnInterpretedValue =>
        renamedSorts.get(u.sort.sortName) match {
          case Some(_) => failwith("cannot handle uninterpreted constants")
          case _ => v
        }
      case _ => v
    }
  }


}
