package tempura.expression

import Core.*
import tempura.helpers.Utils.unexpected
import tempura.helpers.Utils

import scala.annotation.tailrec

object Syntax {
  extension (a: Expr[BoolSort]) {
    infix def ~ : Expr[BoolSort] = Core.mkNot(a)
    infix def \/(bs: Expr[BoolSort]*): Expr[BoolSort] = Core.mkOr(a :: bs.toList)
    infix def /\(bs: Expr[BoolSort]*): Expr[BoolSort] = Core.mkAnd(a :: bs.toList)
    infix def |=(b: Expr[BoolSort]): Expr[BoolSort] = Core.mkImplies(a, b)
    infix def <=>(b: Expr[BoolSort]): Expr[BoolSort] = Core.mkIff(a, b)
  }
  extension (a: Expr[NumericSort]) {
    infix def +(bs: Expr[NumericSort]*): Expr[NumericSort] = Core.mkAdd(a :: bs.toList)
    infix def -(bs: Expr[NumericSort]*): Expr[NumericSort] = {
      bs.toList match {
        case List(t) => Core.mkMinus(a, t)
        case rest => Core.mkMinus(a, Core.mkAdd(rest))
      }
    }
    infix def *(bs: Expr[NumericSort]*): Expr[NumericSort] = Core.mkMul(a :: bs.toList)
    infix def /(b: Expr[NumericSort]): Expr[NumericSort] = Core.mkFraction(a, b)
    infix def >(b: Expr[NumericSort]): Expr[BoolSort] = Core.mkGt(a, b)
    infix def <(b: Expr[NumericSort]): Expr[BoolSort] = Core.mkLt(a, b)
    infix def >=(b: Expr[NumericSort]): Expr[BoolSort] = Core.mkGe(a, b)
    infix def <=(b: Expr[NumericSort]): Expr[BoolSort] = Core.mkLe(a, b)
  }
  extension (a: Expr[BoolSort]*) {
    infix def \/(bs: Expr[BoolSort]*): Expr[BoolSort] = Core.mkOr(a.toList ++ bs.toList)
    infix def /\(bs: Expr[BoolSort]*): Expr[BoolSort] = Core.mkAnd(a.toList ++ bs.toList)
  }

  infix def /\(args: Expr[BoolSort]*): Expr[BoolSort] = Core.mkOr(args.toList)

  infix def \/(args: Expr[BoolSort]*): Expr[BoolSort] = Core.mkAnd(args.toList)

  infix def |=|[X <: Sort[X]](lhs: Expr[X], rhs: Expr[X]): Expr[BoolSort] = Core.mkEq(lhs, rhs)

  infix def |@|[X <: Sort[X], Y <: Sort[Y]](arr: Expr[ArraySort[X, Y]], idx: Expr[X]): Expr[Y] = Core.mkSelect(arr, idx)

  extension [X <: Sort[X], Y <: Sort[Y]](arr: Expr[ArraySort[X, Y]]) {
    infix def @<(idx: Expr[X]): SelectorSyntax[X, Y] = SelectorSyntax(arr, idx)
  }

  case class SelectorSyntax[X <: Sort[X], Y <: Sort[Y]](arr: Expr[ArraySort[X, Y]], idx: Expr[X]) {
    infix def > : Expr[Y] = Core.mkSelect(arr, idx)

    infix def >=(rhs: Expr[Y]): Expr[ArraySort[X, Y]] = Core.mkStore(arr, idx, rhs)
  }

  // some helpers for TypeEnv/InterpEnv to avoid syntactic redundancy
  extension (t: TypeEnv) {
    def newType(bs: Core.BoxedSort): Core.BoxedSort = {
      t.add(bs.sortName, bs)
      bs
    }

    def newType[S <: Core.Sort[S]](s: S): S = {
      t.add(s.sortName, s)
      s
    }
  }

  extension (e: InterpEnv) {
    // Create a new variable
    def newVar[S <: Sort[S]](b: Core.Var[S]): Core.Var[S] = {
      e.add(b.name, b)
      b
    }
    def newVar[S <: Sort[S]](n: String, s: S): Core.Var[S] = {
      val p = Core.Var(n, s)
      e.add(n, p)
      p
    }
    // Create a new variable and automatically name it
    def freshVar[S <: Sort[S]](sort: S): Core.Var[S] = {

      @tailrec
      def aux(pref: String): String =
        val s = Utils.getUniqueName(pref)
        e(s) match {
          case Some(_) => aux(s)
          case None => s
        }

      val varName = aux("_sk")
      e.add(varName, Core.Var(varName, sort))
      Core.Var(varName, sort)
    }
    // Define a new variable and automatically name it
    def freshVar[S <: Sort[S]](sort: S, expr: Expr[S]): Core.Expr[S] = {
      val p = freshVar(sort)
      e.add(p.name, expr)
      expr
    }
    // Create a new variable with a given name and automatically name it
    def newVarDef(n: String, b: BoxedExpr): Core.BoxedExpr = {
      e.add(n, b)
      b
    }
    def newVarDef[S <: Core.Sort[S]](n: String, expr: Core.Expr[S]): Core.Expr[S] = {
      e.add(n, expr)
      expr
    }

    infix def |-[X <: Sort[X]](t: (String, X)): Var[X] = newVar(t._1, t._2)

    infix def ||-[X <: Sort[X]](t: (String, Expr[X])): Expr[X] = newVarDef(t._1, t._2)
  }

  extension (tyE: TypeEnv) {
    infix def |-[X <: Sort[X]](x: X): X = {
      tyE.add(x.sortName, x)
      x
    }
  }

  extension [X <: Sort[X]](f: Expr[FunSort[X]]) {
    def apply(args: (String, BoxedExpr)*): Expr[X] = {
      Core.mkApp(args.toList, f)
    }
  }

  extension (fs: FiniteUniverseSort) {
    infix def %(i: Int): Core.Const[FiniteUniverseSort] = {
      if i < 0 || i > fs.card then 
        unexpected(s"Error: ${fs.toString} has ${fs.card} elements but got ${i}")
      else
        Core.Const(SortValue.FiniteUniverseValue(i, fs))
    }
  }

  //
  // Extractor objects for helping preserve return sorts during pattern-matching
  //
  object And {
    def unapply(e: BoxedExpr): Option[List[Expr[BoolSort]]] = e.e match
      case Lop("and", es, _, _) =>
        Some(es.asInstanceOf[List[Expr[BoolSort]]])
      case _ => None
  }

  object Or {
    def unapply(e: BoxedExpr): Option[List[Expr[BoolSort]]] = e.e match
      case Lop("or", es, _, _) =>
        Some(es.asInstanceOf[List[Expr[BoolSort]]])
      case _ => None
  }

  object Not {
    def unapply(e: BoxedExpr): Option[Expr[BoolSort]] = e.e match
      case Uop("not", x, _) =>
        Some(x.asInstanceOf[Expr[BoolSort]])
      case _ => None
  }

  object Implies {
    def unapply(e: BoxedExpr): Option[(Expr[BoolSort], Expr[BoolSort])] = e.e match
      case Bop("=>", a, b, _) =>
        Some((a.asInstanceOf[Expr[BoolSort]], b.asInstanceOf[Expr[BoolSort]]))
      case _ => None
  }

  object Globally {
    def unapply(e: BoxedExpr): Option[Expr[BoolSort]] = e.e match {
      case Core.Uop("globally", gBody, Core.BoolSort()) =>
        Some(gBody.asInstanceOf[Expr[BoolSort]])
      case _ => None
    }
  }
  
  object Eventually {
    def unapply(e: BoxedExpr): Option[Expr[BoolSort]] = e.e match {
      case Core.Uop("eventually", eBody, Core.BoolSort()) =>
        Some(eBody.asInstanceOf[Expr[BoolSort]])
      case _ => None
    }
  }

  object BoolExpr {
    def unapply(e: BoxedExpr): Option[Expr[BoolSort]] =
      e.unify(Core.boolSort)
  }

  // Conversion between integers and our own Numeric sort-values
  given intToNumber: Conversion[Int, Expr[Core.NumericSort]] with
    override def apply(x: Int): Expr[NumericSort] =
      Core.mkNumber(x)

}
