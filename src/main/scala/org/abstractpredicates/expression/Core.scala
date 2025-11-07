package org.abstractpredicates.expression

import org.abstractpredicates.helpers.Utils
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.expression.Core.*
import org.abstractpredicates.helpers.Utils.*
import scala.annotation.tailrec
import scala.collection.Set
import scala.reflect.ClassTag
import cats.implicits.*

object Core {
  sealed trait Sort[T <: Sort[T]](val sortName: String) {
    val ct: ClassTag[T]

    // sort-level unification
    def unify[O <: Sort[O]](otherSort: O): Option[T] = {
      this.ct.unapply(otherSort) match {
        case Some(s) => Some(s)
        case None => None
      }
    }

    def unifyExpr[U <: Sort[U]](expr: Expr[U]): Option[Expr[T]] = {
      this.ct.unapply(expr.sort) match {
        case Some(s) => Some(expr.asInstanceOf[Expr[T]])
        case None => None
      }
    }

    override def toString: String = sortName
  }

  trait BoxedExpr {
    type T <: Sort[T]
    val e: Expr[T]
    val sort: T

    def unify[U <: Sort[U]](u: U): Option[Expr[U]] = {
      sort.unify(u) match {
        case Some(sort2) =>
          Some(this.e.asInstanceOf[Expr[U]])
        case _ => None
      }
    }

    // Because of auto-conversions if we overload by 
    // the following method Scala compiler will complain 
    // def unify(bs: BoxedSort): Option[Expr[bs.S]] = unify[bs.S](bs.sort)

    def unbox: Expr[T] = this.e

    override def equals(obj: Any): Boolean = obj match {
      case that: BoxedExpr => this.e == that.e
      case that: Expr[?] => this.e == that
      case _ => false
    }

    override def hashCode(): Int = {
      e.hashCode()
    }

    override def toString: String = e.toString
  }

  object BoxedExpr {

    def make[X <: Sort[X]](t: X, expr: Expr[X]): BoxedExpr {type T = X} = {
      new BoxedExpr {
        type T = X
        override val e: Expr[X] = expr
        override val sort: T = t
      }
    }
  }

  // Base sort 1: Numeric constants
  case class NumericSort() extends Sort[NumericSort]("Int") {
    override val ct: ClassTag[NumericSort] = summon[ClassTag[NumericSort]]

    override def equals(obj: Any): Boolean = {
      obj match {
        case that: NumericSort =>
          this.ct.unapply(that).isDefined
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }
    }

    override def hashCode(): Int = "Int".hashCode()
  }

  // Base sort 2: boolean sort
  case class BoolSort() extends Sort[BoolSort]("Bool") {
    override val ct: ClassTag[BoolSort] = summon[ClassTag[BoolSort]]

    override def equals(obj: Any): Boolean = {
      obj match {
        case that: BoolSort =>
          this.ct.unapply(that).isDefined
        case that: BoxedSort =>
          equals(that.sort)
        case _ => super.equals(obj)
      }
    }

    override def hashCode(): Int = "Bool".hashCode()
  }

  // Compound sorts.
  case class ArraySort[D <: Sort[D], R <: Sort[R]](val domainSort: D, val rangeSort: R)
    extends Sort[ArraySort[D, R]]("Array " + domainSort.toString + " " + rangeSort.toString) {

    override val ct: ClassTag[ArraySort[D, R]] = summon[ClassTag[ArraySort[D, R]]]

    override def unify[O <: Sort[O]](otherSort: O): Option[ArraySort[D, R]] = {
      this.ct.unapply(otherSort) match {
        case Some(ArraySort(domain, range)) =>
          (domain.unify(domainSort), range.unify(rangeSort)).tupled match {
            case Some(d, r) => Some(ArraySort[D, R](d, r))
            case None => None
          }
        case None => None
      }
    }

    override def unifyExpr[U <: Sort[U]](expr: Expr[U]): Option[Expr[ArraySort[D, R]]] = {
      expr.unify(this)
    }

    override def equals(that: Any): Boolean = {
      that match {
        case thatArr: ArraySort[_, _] =>
          domainSort == thatArr.domainSort && rangeSort == thatArr.rangeSort
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }
    }

    override def hashCode(): Int =
      (domainSort, rangeSort).##

    given domain: D = domainSort

    given range: R = rangeSort
  }

  // this sort refers to constant-valued functions in SMTLIB, which are actual functions
  // due to limitations of scala's type system, we only type a function (really a macro) by its return type.
  case class FunSort[R <: Sort[R]](val domainSort: List[BoxedSort], val rangeSort: R)
    extends Sort[FunSort[R]]("-> " + "(" + domainSort.map(x => "(" + x.toString + ")").mkString(" ") + ") " + rangeSort.toString) {
    override val ct: ClassTag[FunSort[R]] = summon[ClassTag[FunSort[R]]]

    override def unify[O <: Sort[O]](otherSort: O): Option[FunSort[R]] = {
      this.ct.unapply(otherSort) match {
        case Some(FunSort(domains, range)) =>
          if domains.size != domainSort.size then None else
            (domains.zip(domainSort).traverse((x, y) => y.sort.unify(x.sort).map(x => x.box)), rangeSort.unify(range)).tupled match {
              case Some(domainUnified, rangeUnified) =>
                Some(FunSort[R](domainUnified, rangeUnified))
              case None => None
            }
        case None => None
      }
    }

    override def unifyExpr[U <: Sort[U]](expr: Expr[U]): Option[Expr[FunSort[R]]] = {
      expr.unify(this)
    }

    override def equals(obj: Any): Boolean = {
      obj match {
        case f@FunSort(_, _) =>
          this.domainSort == f.domainSort && this.rangeSort == f.rangeSort
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }
    }

    override def hashCode(): Int =
      (domainSort, rangeSort).##

    given range: R = rangeSort
  }

  case class UnInterpretedSort(name: String, numArgs: Int) extends Sort[UnInterpretedSort](name) {
    override val ct: ClassTag[UnInterpretedSort] = summon[ClassTag[UnInterpretedSort]]

    override def equals(obj: Any): Boolean = {
      obj match {
        case that: UnInterpretedSort =>
          this.name == that.name && this.numArgs == that.numArgs
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }
    }

    override def hashCode(): Int = (name, numArgs).##
  }

  // Other stuff
  case class FiniteUniverseSort(name: String, card: Int) extends Sort[FiniteUniverseSort](name) {
    override val ct: ClassTag[FiniteUniverseSort] = summon[ClassTag[FiniteUniverseSort]]

    def toDatatypeSort: Core.DatatypeConstructorSort = {
      val constructors = Utils.mkEnumNames(name, card).map(x => Core.constructor(x, List()))
      DatatypeConstructorSort(name, constructors)
    }

    override def equals(obj: Any): Boolean = {
      obj match {
        case that: FiniteUniverseSort =>
          this.name == that.name && this.card == that.card
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }
    }

    override def hashCode(): Int = (name, card).##
  }

  class Constructor(val name: String, val args: List[(String, BoxedSort)]) {
    override def equals(obj: Any): Boolean =
      obj match {
        case cons: Constructor =>
          cons.name == this.name && cons.args == this.args
        case _ => false
      }

    override def hashCode(): Int = (name, args).##
  }

  case class InstantiatedConstructor(val constructor: Constructor, val params: List[BoxedExpr]) {
    def getConstructor: Constructor = constructor

    def getName: String = constructor.name

    def getParams: List[BoxedExpr] = params

    def check: Boolean = {
      if (params.size != constructor.args.size) then false
      else {
        params.zip(constructor.args).traverse(
          x => x._1.unify(x._2._2)
        ).isDefined
      }
    }

    override def equals(obj: Any): Boolean =
      obj match {
        case ic: InstantiatedConstructor =>
          ic.constructor == this.constructor && ic.params == this.params
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }

    override def hashCode(): Int = (constructor, params).##
  }


  case class DatatypeConstructorSort(val name: String, var constructors: List[Constructor]) extends Sort[DatatypeConstructorSort](name) {
    override val ct: ClassTag[DatatypeConstructorSort] = summon[ClassTag[DatatypeConstructorSort]]

    def addConstructor(cons: Constructor): Unit = {
      constructors = cons :: constructors
    }

    def getConstructors: List[Constructor] = constructors

    def lookupConstructor(consName: String): Option[Constructor] = {
      constructors.find(x => x.name == consName)
    }

    override def equals(obj: Any): Boolean =
      obj match {
        case dt: DatatypeConstructorSort =>
          dt.name == this.name && dt.constructors == this.constructors
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }

    override def hashCode(): Int = (name, constructors).##
  }

  // for define-sort SMTLIB keyword
  case class AliasSort[S <: Sort[S]](val name: String, val args: List[BoxedSort], val underlyingSort: S) extends Sort[AliasSort[S]](name) {
    override val ct: ClassTag[AliasSort[S]] = summon[ClassTag[AliasSort[S]]]

    given deAlias: S = underlyingSort

    override def equals(obj: Any): Boolean =
      obj match {
        case alias: AliasSort[x] =>
          this.name == alias.name && this.args == alias.args && this.underlyingSort == alias.underlyingSort
        case that: BoxedSort =>
          equals(that.sort)
        case _ => false
      }

    override def hashCode(): Int = (name, args).##
  }

  enum SortValue[S <: Sort[S]](val sort: S) {
    case BoolValue(b: Boolean) extends SortValue[BoolSort](BoolSort())
    case NumericValue(n: Int) extends SortValue[NumericSort](NumericSort())
    case ArrayValue[D <: Sort[D], R <: Sort[R]](default: Expr[R], s: ArraySort[D, R])
      extends SortValue[ArraySort[D, R]](s)
    case FiniteUniverseValue(idx: Int, s: FiniteUniverseSort) extends SortValue[FiniteUniverseSort](s)
    case UnInterpretedValue(name: String, s: UnInterpretedSort) extends SortValue[UnInterpretedSort](s)
    case AliasSortValue[X <: Sort[X]](name: String, s: AliasSort[X]) extends SortValue[AliasSort[X]](s)
    case DatatypeValue(constructorInst: InstantiatedConstructor, s: DatatypeConstructorSort) extends SortValue[DatatypeConstructorSort](s)
  }

  trait BoxedSort {
    type S <: Sort[S]
    val sort: S

    def unbox(): S = this.sort

    def unify(other: BoxedSort): Option[S] = {
      if this.sort.equals(other.sort) then
        Some(other.asInstanceOf[S])
      else None
    }

    def unify[T <: Sort[T]](other: T): Option[S] = {
      if this.sort.equals(other.sort) then
        Some(other.asInstanceOf[S])
      else None
    }

    override def toString: String = {
      this.sort.toString
    }

    override def equals(otherAny: Any): Boolean = {
      otherAny match {
        case other: BoxedSort =>
          this.sort.unify(other) match {
            case Some(t) => this.sort == other.sort
            case None => false
          }
        case other: Sort[x] =>
          other.unify(this.sort).isDefined && other == this.sort
        case _ => false
      }
    }


    override def hashCode(): Int =
      // delegate to underlying sort to keep equals/hashCode consistent
      sort.hashCode()

  }

  object BoxedSort {
    def make[T <: Sort[T]](t: T): BoxedSort {type S = T} = {
      new BoxedSort {
        override type S = T
        override val sort: T = t
      }
    }
  }

  import scala.Conversion

  // Implicit conversion between a sort and its boxed representation

  extension [T <: Sort[T]](a: T)
    def box: BoxedSort {type S = T} =
      BoxedSort.make(a)

  given boxSort[A <: Sort[A]]: Conversion[A, BoxedSort {type S = A}] with
    def apply(a: A): BoxedSort {type S = A} = BoxedSort.make(a)

  given unboxSort[A <: Sort[A]]: Conversion[BoxedSort {type S = A}, A] with
    def apply(ba: BoxedSort {type S = A}): A = ba.sort

  // Implicit conversion between a sort and its boxed representation
  given boxExpr[A <: Sort[A]]: Conversion[Expr[A], BoxedExpr {type T = A}] with
    def apply(expr: Expr[A]): BoxedExpr {type T = A} =
      BoxedExpr.make[A](expr.sort, expr)

  given unboxExpr[A <: Sort[A]]: Conversion[BoxedExpr {type T = A}, Expr[A]] with
    def apply(ba: BoxedExpr {type T = A}): Expr[A] =
      ba.e

  // Explicit conversions
  extension [A <: Sort[A]](expr: Expr[A])
    def box(): BoxedExpr {type T = A} =
      BoxedExpr.make(expr.sort, expr)

  class Env[T](n: String, d: scala.collection.mutable.Map[String, T]) {
    private val m: scala.collection.mutable.Map[String, T] = d
    private val name: String = n

    // update hooks for backend solvers.
    // these are not copy-constructed upon ++@
    private var updateHook: Option[(String, T) => String] = None
    private var history: List[((String, T), String)] = List()

    def registerUpdateHook(f: (String, T) => String) =
      updateHook = Some(f)

    def getUpdateHook: Option[(String, T) => String] = updateHook

    def getHistory: List[((String, T), String)] = history

    def this(n: String) = this(n, scala.collection.mutable.Map[String, T]())

    def this() = this("<env>", scala.collection.mutable.Map[String, T]())

    def this(d: scala.collection.mutable.Map[String, T]) = this("<env>", d)

    def this(l: List[(String, T)]) = {
      this(scala.collection.mutable.Map.from(l))
    }

    def this(n: String, l: List[(String, T)]) = {
      this(n, scala.collection.mutable.Map.from(l))
    }


    // overrides the old value if exists
    def add(s: String, e: T): Env[T] = {
      this.m.put(s, e)
      this.updateHook match {
        case Some(f) =>
          val result = f(s, e)
          history = ((s, e), result) :: history
        case _ => ()
      }
      this
    }

    def lookup(s: String): Option[T] = {
      this.m.get(s)
    }

    def contains(s: String): Boolean = {
      m.contains(s)
    }

    def size: Int = {
      m.size
    }

    def foreach(f: ((String, T)) => Unit): Unit = {
      m.foreach(f)
    }

    // other values will override this values
    // a ++@ b means b's values take precedence
    def ++@(other: Env[T]): Env[T] = {
      new Env[T]("mergedFrom[" + this.name + ";" + other.name + "]", this.m ++ other.m)
    }

    def apply(key: String): Option[T] = {
      this.lookup(key)
    }

    def remove(key: String): Option[T] = {
      this.m.remove(key)
    }

    def getName: String = {
      this.name
    }

    def toList: List[(String, T)] = {
      this.m.toList
    }

    // those in list e will override (i.e., take precedence)
    // existing values
    def addFromList(e: List[(String, T)]): Env[T] = {
      e match {
        case a :: t =>
          this.add(a._1, a._2)
          addFromList(t)
          this
        case List() =>
          this
      }
    }

    override def toString: String = {
      "[< " + this.name + " {" + this.m.toString() + "} >]"
    }

    def copy(): Env[T] = {
      val newMap = d.clone()
      Env[T](String(n), newMap)
    }
  }

  type InterpEnv = Env[BoxedExpr]
  type TypeEnv = Env[BoxedSort]
  type InterpList = List[(String, BoxedExpr)]

  def emptyTypeEnv: TypeEnv = new Env()

  def emptyInterpEnv: InterpEnv = new Env[BoxedExpr]()

  extension [T](l: List[(String, T)])
    def toEnv = new Env[T](l)

  // Generified expressions. A denotes the return type of the expression
  // after evaluation.

  // A note about function handling.
  // In general, SMTLIB is a first-order language, so function symbols are handled a bit differently
  // and unlike constants, cannot be passed around freely like terms. There are two ways to represent
  // a function in our IR: 
  // (1) an Expr.Macro[t] instance, which denotes a function with a given definition 
  // (in Z3-lingo, an uninterpreted function with an axiom) of type Expr[t] --- the body itself needs
  // to be scoped appropriately, as its vocabulary ranges over both pre-defined symbols _as well as_
  // the function arguments.  
  // 
  // (2) an Expr.Var[FunSort[t]] instance, which denotes an uninterpreted function (that is, a function
  // without a body. Its arguments are captured inside the ``sort`` field of the instance, which has
  // type FunSort[t].
  //
  // Different from Z3, which has a special FunDecl<T> type, and SMTInterpol, which differentiates between
  // a TermVariable and a Variable (the latter is a function symbol that cannot be used as a term),
  // our functions _are AST terms_. But special treatment is afforded to cases (1) and (2) above,
  // to ensure that our language is truly first-order (which is to say that users can construct higher-order expressions
  // using our AST, but the solver-related facilities cannot, in general, handle such expressions).  
  //
  // During the initial compilation into our IR, the VMTParser resolves arbitrary function symbol invocations
  // into either (2), if no function of the same name has been previously defined, or (1), if a function symbol
  // has a previously defined meaning (via define-fun primitive). That is, if we specify all definitions in a VMTLIB
  // file first (which is what we do usually), the parser will greedily inline all macro definitions in-place.
  // All declared but un-defined function symbols are afforded treatment (2), that is, their application becomes
  // an application of a Var[FunSort[t]] instance.
  //
  // All function declarations and definitions are stored in the InterpEnv environment --- we can look up a string,
  // which denotes the function name, and its lookup either yields a Var[FunSort[t]] instance, a Macro[t] instance, 
  // or something else.  In the first two cases, we know the symbol we looked up resolves to a function, and in the
  // last case, the symbol must be a non-function (e.g., an ordinary boolean state variable).  
  sealed trait Expr[A <: Sort[A]](val sort: A) {

    // returns a stream of AST subtrees of the current AST.
    def toLazyList: LazyList[Expr[? <: Sort[?]]] =
      this #:: (this match {
        case Var(_, _) | Const(_) => LazyList.empty
        case e: ArraySelect[x, y] => e.a.toLazyList #::: e.index.toLazyList
        case e: ArrayStore[x, y] => e.a.toLazyList #::: e.index.toLazyList #::: e.value.toLazyList
        case e: Top[x, y, z, w] => e.a.toLazyList #::: e.b.toLazyList #::: e.c.toLazyList
        case e: Bop[x, y, z] => e.lhs.toLazyList #::: e.rhs.toLazyList
        case e: Uop[x, y] => e.subExpr.toLazyList
        case e@Lop(_, _, _, _) => e.subExpr.map(x => x.toLazyList).reduce((x, y) => x #::: y)
        case e: Macro[y] => e.expr.toLazyList
        case e: Substitute[y] => e.expr.toLazyList
        case DatatypeConstructorRecognizer(_, _, _) => ???
        case Forall(_, _) => ???
        case Exists(_, _) => ???
      })

    // return the underlying sort of an Expr[X] instance.

    given sortFromExpr: A = sort
  }

  case class Var[A <: Sort[A]](name: String, s: A) extends Expr[A](s) {

    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case v@Var(_, _) => v.name == this.name && v.sort.unify(this.sort).isDefined
        case _ => false
      }
    }

    override def hashCode(): Int = (name, s).##
  }

  case class DatatypeConstructorRecognizer(dt: DatatypeConstructorSort,
                                           constructorName: String,
                                           subExpr: Expr[DatatypeConstructorSort])
    extends Expr[FunSort[BoolSort]](funSort(List(dt), BoolSort())) {

    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case dsr: DatatypeConstructorRecognizer =>
          this.dt == dsr.dt &&
            this.constructorName == dsr.constructorName &&
            this.subExpr == dsr.subExpr
        case _ => false
      }
    }

    override def hashCode(): Int = (dt, constructorName, subExpr).##
  }

  //
  // Technically, (forall ...) and (exists ...) should be treated as
  // two levels in this AST where forall, exists denote a Macro and
  // a forall/exists-call denote a Substitution. That is, forall/exists
  // are essentially functions, and quantified formulas are function
  // applications. But considering how often we use them, it seems
  // like they might warrant their own AST node instead of having
  // to suffer with AST bloating.
  case class Forall(vars: List[(String, BoxedSort)], body: Expr[BoolSort]) extends Expr[BoolSort](BoolSort()) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case f: Forall => f.vars == this.vars && f.body == this.body
        case _ => false
      }
    }

    override def hashCode(): Int = (vars, body).##
  }

  case class Exists(vars: List[(String, BoxedSort)], body: Expr[BoolSort]) extends Expr[BoolSort](BoolSort()) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case e: Exists => e.vars == this.vars && e.body == this.body
        case _ => false
      }
    }

    override def hashCode(): Int = (vars, body).##
  }

  // Similarly, ArraySelect and ArrayStore are binary and ternary operations
  // that can be implemented using Bop and Top. But due to how common they are
  // we feel like they warrant their own AST node for convenience reasons.
  // Basic operations on SMTLIB-style arrays, again represented as HOASed lambdas.
  // Array is of type X => Y
  // Selecting an element of type X from array X->Y yields expression of type Y
  case class ArraySelect[X <: Sort[X], Y <: Sort[Y]](a: Expr[ArraySort[X, Y]], index: Expr[X])
                                                    (using domainSort: X, rangeSort: Y) extends Expr[Y](rangeSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case e: ArraySelect[_, _] =>
          e.a == this.a && e.index == this.index
        case _ => false
      }
    }

    override def hashCode(): Int = (a, index).##
  }

  // Storing a (key, val) pair into array yields a new array
  case class ArrayStore[X <: Sort[X], Y <: Sort[Y]](a: Expr[ArraySort[X, Y]], index: Expr[X], value: Expr[Y])
                                                   (using domainSort: X, rangeSort: Y)
    extends Expr[ArraySort[X, Y]](ArraySort[X, Y](domainSort, rangeSort)) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case e: ArrayStore[_, _] =>
          e.a == this.a &&
            e.index == this.index &&
            e.value == this.value
        case _ => false
      }
    }

    override def hashCode(): Int = (a, index, value).##
  }

  // Datatype accessors should just be Const-terms with a special SortValue
  case class Const[A <: Sort[A]](sortValue: SortValue[A]) extends Expr[A](sortValue.sort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case c @ Const(_) => c.sortValue == this.sortValue
        case _ => false
      }
    }

    override def hashCode(): Int = sortValue.##
  }

  case class Top[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z], W <: Sort[W]](name: String, a: Expr[X], b: Expr[Y], c: Expr[Z], retSort: W)
                                                                        (using sortA: X, sortB: Y, sortC: Z)
    extends Expr[W](retSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case t@Top(_, _, _, _, _) =>
          t.name == this.name && t.a == this.a && t.b == this.b && t.c == this.c && t.retSort == this.retSort
        case _ => false
      }
    }

    override def hashCode(): Int = (name, a, b, c, retSort).##
  }

  case class Bop[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z]](name: String, lhs: Expr[X], rhs: Expr[Y], retSort: Z)
                                                          (using sortLHS: X, sortRHS: Y)
    extends Expr[Z](retSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case b@Bop(_, _, _, _) =>
          b.name == this.name && b.lhs == this.lhs && b.rhs == this.rhs && b.retSort == this.retSort
        case _ => false
      }
    }

    override def hashCode(): Int = (name, lhs, rhs, retSort).##
  }

  case class Uop[X <: Sort[X], Y <: Sort[Y]](name: String, subExpr: Expr[X], retSort: Y)(using sortDom: X)
    extends Expr[Y](retSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case u@Uop(_, _, _) =>
          u.name == this.name && u.subExpr == this.subExpr && u.retSort == this.retSort
        case _ => false
      }
    }

    override def hashCode(): Int = (name, subExpr, retSort).##
  }

  case class Lop[X <: Sort[X], Y <: Sort[Y]](name: String, subExpr: List[Expr[X]], val argSort: X, val retSort: Y)(using sort: X)
    extends Expr[Y](retSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case l@Lop(_, _, _, _) =>
          l.name == this.name && l.subExpr == this.subExpr && l.argSort == this.argSort && l.retSort == this.retSort
        case _ => false
      }
    }

    override def hashCode(): Int = (name, subExpr, argSort, retSort).##
  }

  // generalizes all forms of second-order objects.
  case class Macro[Y <: Sort[Y]](name: String, vars: List[(String, BoxedSort)], expr: Expr[Y])(using sort: FunSort[Y])
    extends Expr[FunSort[Y]](sort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case m@Macro(_, _, _) =>
          m.name == this.name && m.vars == this.vars && m.expr == this.expr
        case _ => false
      }
    }

    override def hashCode(): Int = (name, vars, expr).##
  }

  // generalizes all forms of applying second-order objects.
  case class Substitute[Y <: Sort[Y]](attribute: String, varBindings: List[(String, BoxedExpr)], expr: Expr[FunSort[Y]])
                                     (using macroSort: FunSort[Y]) extends Expr[Y](macroSort.rangeSort) {
    override def equals(obj: Any): Boolean = {
      obj match {
        case be: BoxedExpr => equals(be.e)
        case s@Substitute(_, _, _) =>
          s.attribute == this.attribute && s.varBindings == this.varBindings && s.expr == this.expr
        case _ => false
      }
    }
  }


  //
  // Methods for helping create expressions
  //

  def mkTrue: Expr[BoolSort] =
    Core.Const(SortValue.BoolValue(true))

  def mkFalse: Expr[BoolSort] =
    Core.Const(SortValue.BoolValue(false))

  def mkNumber(n: Int): Expr[NumericSort] =
    Core.Const(SortValue.NumericValue(n))

  def mkVar[X <: Sort[X]](name: String, sort: X): Expr[X] =
    Core.Var(name, sort)

  def mkSelect[X <: Sort[X], Y <: Sort[Y]](arr: Expr[ArraySort[X, Y]], index: Expr[X]): Expr[Y] =
    Core.ArraySelect[X, Y](arr, index)(using arr.sort.domainSort, arr.sort.rangeSort)

  def mkStore[X <: Sort[X], Y <: Sort[Y]](arr: Expr[ArraySort[X, Y]], index: Expr[X], value: Expr[Y]): Expr[ArraySort[X, Y]] =
    Core.ArrayStore(arr, index, value)(using arr.sort.domainSort, arr.sort.rangeSort)

  def mkTop[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z], W <: Sort[W]](name: String, operand1: Expr[X], operand2: Expr[Y], operand3: Expr[Z], retSort: W): Expr[W] =
    Core.Top[X, Y, Z, W](name, operand1, operand2, operand3, retSort)(using operand1.sort, operand2.sort, operand3.sort)

  def mkBop[X <: Sort[X], Y <: Sort[Y], Z <: Sort[Z]](name: String, lhs: Expr[X], rhs: Expr[Y], retSort: Z): Expr[Z] =
    Bop[X, Y, Z](name, lhs, rhs, retSort)(using lhs.sort, rhs.sort)

  def mkUop[X <: Sort[X], Y <: Sort[Y]](name: String, subExpr: Expr[X], retSort: Y): Expr[Y] =
    Uop[X, Y](name, subExpr, retSort)(using subExpr.sort)

  def mkEq[X <: Sort[X]](lhs: Expr[X], rhs: Expr[X]): Expr[BoolSort] =
    Bop[X, X, BoolSort]("=", lhs, rhs, BoolSort())(using lhs.sort, rhs.sort)

  def mkAnd(args: List[Expr[BoolSort]]): Expr[BoolSort] =
    mkLop("and", args, BoolSort(), BoolSort())

  def mkOr(args: List[Expr[BoolSort]]): Expr[BoolSort] =
    mkLop("or", args, BoolSort(), BoolSort())

  def mkNot(arg: Expr[BoolSort]): Expr[BoolSort] =
    mkUop("not", arg, BoolSort())

  def mkImplies(lhs: Expr[BoolSort], rhs: Expr[BoolSort]): Expr[BoolSort] =
    mkBop("=>", lhs, rhs, BoolSort())

  def mkIte[X <: Sort[X]](cond: Expr[BoolSort], thenBranch: Expr[X], elseBranch: Expr[X]): Expr[X] =
    mkTop("ite", cond, thenBranch, elseBranch, thenBranch.sort)

  def mkAdd(args: List[Expr[NumericSort]]): Expr[NumericSort] =
    mkLop("+", args, Core.NumericSort(), Core.NumericSort())

  def mkMinus(lhs: Expr[NumericSort], rhs: Expr[NumericSort]): Expr[NumericSort] =
    mkBop("-", lhs, rhs, Core.NumericSort())

  def mkMul(args: List[Expr[NumericSort]]): Expr[NumericSort] =
    mkLop("*", args, Core.NumericSort(), Core.NumericSort())

  def mkNegative(term: Expr[Core.NumericSort]): Expr[Core.NumericSort] =
    mkUop("-", term, Core.NumericSort())

  def mkGt(lhs: Expr[NumericSort], rhs: Expr[NumericSort]): Expr[BoolSort] =
    mkBop(">", lhs, rhs, Core.BoolSort())

  def mkGe(lhs: Expr[NumericSort], rhs: Expr[NumericSort]): Expr[BoolSort] =
    mkBop(">=", lhs, rhs, Core.BoolSort())

  def mkLt(lhs: Expr[NumericSort], rhs: Expr[NumericSort]): Expr[BoolSort] =
    mkBop("<", lhs, rhs, Core.BoolSort())

  def mkLe(lhs: Expr[NumericSort], rhs: Expr[NumericSort]): Expr[BoolSort] =
    mkBop("<=", lhs, rhs, Core.BoolSort())

  def mkFraction(numerator: Expr[Core.NumericSort], denominator: Expr[Core.NumericSort]): Expr[Core.NumericSort] =
    mkBop("/", numerator, denominator, Core.NumericSort())

  def mkLop[X <: Sort[X], Y <: Sort[Y]](name: String, subExpr: List[Expr[X]], argSort: X, retSort: Y): Expr[Y] =
    Lop[X, Y](name, subExpr, argSort, retSort)(using argSort)

  // This is a Z3-specific array extension that turns arbitrary functions into arrays
  // A function's argument list length is unknown at compile-time, but with help from
  // Z3's internal API (which keeps track of the array sort), we can recursively parse 
  // the function's sort back into an ArraySort instance ( in particular, `D` here would
  // be dynamically determined by `Z3Solver.liftSort`. However, we lose the ability
  // to guarantee that FunSort[R]'s domain sorts correspond to the array's domain sorts.
  def mkAsArray[D <: Sort[D], R <: Sort[R]](func: Expr[FunSort[R]], aSort: ArraySort[D, R]): Expr[ArraySort[D, R]] =
    mkUop("as-array", func, aSort)

  def mkConst[S <: Sort[S]](const: SortValue[S]): Expr[S] =
    Const(const)

  def mkConstArray[D <: Sort[D], R <: Sort[R]](domainSort: D, constVal: Expr[R]): Expr[ArraySort[D, R]] =
    mkConst(SortValue.ArrayValue(constVal, arraySort(domainSort, constVal.sort)))

  // In many cases there are operations like
  //  (<op> <f> <args for f>)
  // This is technically a second-order operation. But
  // we support it by treating it as an AST term of depth-2:
  // (BOP <op> <f> <f args>)
  // 
  def mkArrayMap[D <: Sort[D], R <: Sort[R], FR <: Sort[FR]](arr: List[Expr[ArraySort[D, R]]], arrDom: D, arrRange: R, f: Expr[FunSort[FR]]): Expr[ArraySort[D, FR]] =
    f match {
      case f1@Core.Macro(fName, _, _) =>
        mkBop("map", f, mkLop(fName, arr, arraySort(arrDom, arrRange), f.sort.rangeSort), arraySort(arrDom, f.sort.rangeSort))
      case f2@Core.Var(fName, _) =>
        mkBop("map", f, mkLop(fName, arr, arraySort(arrDom, arrRange), f.sort.rangeSort), arraySort(arrDom, f.sort.rangeSort))
      case _ =>
        unsupported(s"mkArrayMap: map(f=${f.toString}, ...) is not mapping over a function.")
    }

  def mkMacro[Y <: Sort[Y]](name: String, vars: List[(String, BoxedSort)], expr: Expr[Y]): Expr[FunSort[Y]] =
    Macro[Y](name, vars, expr)(using toFunSort(vars, expr.sort))

  def mkForall(boundVars: List[(String, BoxedSort)], expr: Core.Expr[Core.BoolSort]): Core.Expr[Core.BoolSort] =
    Forall(boundVars, expr)

  def mkExists(boundVars: List[(String, BoxedSort)], expr: Core.Expr[Core.BoolSort]): Core.Expr[Core.BoolSort] =
    Exists(boundVars, expr)

  def mkSubst[Y <: Sort[Y]](attr: String, bindings: List[(String, BoxedExpr)], macroExpr: Expr[FunSort[Y]]): Expr[Y] =
    Substitute[Y](attr, bindings, macroExpr)(using macroExpr.sort)

  def mkApp[Y <: Sort[Y]](domain: List[(String, BoxedSort)], macroExpr: Macro[Y]): Expr[Y] =
    Core.mkSubst("app",
      domain.map(x => (x._1, Core.mkVar(x._1, x._2))),
      Core.mkVar(macroExpr.name, macroExpr.sort)
    )

  //
  // (Experimental and Z3-only)
  // Cardinality constraints
  //

  def mkAtMost(i: Int, vars: List[Core.Var[Core.BoolSort]]): Core.Expr[Core.BoolSort] =
    Core.mkBop("at-most", Core.mkConst(i), Core.mkLop("at-most", vars, Core.BoolSort(), Core.BoolSort()), Core.BoolSort())

  def mkAtLeast(i: Int, vars: List[Core.Var[Core.BoolSort]]): Core.Expr[Core.BoolSort] =
    Core.mkBop("at-least", Core.mkConst(i), Core.mkLop("at-least", vars, Core.BoolSort(), Core.BoolSort()), Core.BoolSort())

  // 
  // helper methods for creating sorts 
  //

  def numericSort: BoxedSort {type S = NumericSort} = BoxedSort.make(NumericSort())

  def boolSort: BoxedSort {type S = BoolSort} = BoxedSort.make(BoolSort())

  def arraySort[D <: Sort[D], R <: Sort[R]](d: D, r: R): BoxedSort {type S = ArraySort[D, R]} = BoxedSort.make(ArraySort[D, R](d, r))

  def uSort(name: String, numArgs: Int): BoxedSort {type S = UnInterpretedSort} = BoxedSort.make(UnInterpretedSort(name, numArgs))

  def mkDatatypeRecognizer(dt: DatatypeConstructorSort, constructorName: String, arg: Expr[DatatypeConstructorSort]): Expr[FunSort[BoolSort]] =
    DatatypeConstructorRecognizer(dt, constructorName, arg)

  def mkDatatypeAccessor(dt: DatatypeConstructorSort, constructor: InstantiatedConstructor): Expr[DatatypeConstructorSort] =
    Const(SortValue.DatatypeValue(constructor, dt))

  def funSort[R <: Sort[R]](domainSort: List[BoxedSort], rangeSort: R): BoxedSort {type S = FunSort[R]} = BoxedSort.make(FunSort[R](domainSort, rangeSort))


  def toFunSort[R <: Sort[R]](domain: List[(String, BoxedSort)], rangeSort: R): BoxedSort {type S = FunSort[R]} =
    funSort(domain.map(_._2), rangeSort)

  def finiteSort(name: String, cardinality: Int): BoxedSort {type S = FiniteUniverseSort} = BoxedSort.make(FiniteUniverseSort(name, cardinality))

  def datatypeSort(name: String, constructors: List[Constructor]): BoxedSort {type S = DatatypeConstructorSort} = BoxedSort.make(DatatypeConstructorSort(name, constructors))

  def constructor(name: String, args: List[(String, BoxedSort)]): Constructor = Constructor(name, args)

  def constructors(args: List[(String, List[(String, BoxedSort)])]): List[Constructor] = args.map(x => constructor(x._1, x._2))

  def instantiatedConstructor(cons: Constructor, params: List[BoxedExpr]): InstantiatedConstructor = InstantiatedConstructor(cons, params)

  def uninterpreted(name: String, sort: Core.UnInterpretedSort): SortValue[UnInterpretedSort] = SortValue.UnInterpretedValue(name, sort)

  def unifyTerms[S <: Core.Sort[S]](a: List[BoxedExpr], sort: S): Option[List[Core.Expr[S]]] = {
    a.traverse(x => x.unify(sort))
  }

  given bConversion: Conversion[Boolean, SortValue.BoolValue] with
    def apply(b: Boolean): SortValue.BoolValue = SortValue.BoolValue(b)

  given nConversion: Conversion[Int, SortValue.NumericValue] with
    def apply(a: Int): SortValue.NumericValue = SortValue.NumericValue(a)

  given aConversion[D <: Sort[D], R <: Sort[R]]: Conversion[(Expr[R], ArraySort[D, R]), SortValue.ArrayValue[D, R]] with
    def apply(e: (Expr[R], ArraySort[D, R])) = SortValue.ArrayValue(e._1, e._2)


} 