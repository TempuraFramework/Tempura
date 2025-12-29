package tempura.abstraction

/**
 * This is an example of an interval domain implementation inside our abstract interpretation framework.
 * The abstract domain is the domain of intervals, with each domain element being a `case class Interval`
 * object. The distinguished bottom element is an inconsistant interval Interval(1, 0).
 *
 * The concrete domain is the possibly infinite set of integers, which we represent finitely using `Set[Interval]`.
 * The empty set is the bottom element of the concrete domain, which coincides with the bottom element
 * of the abstract domain. We define a helper class called `TVInt`, which provides ability to express + infinity
 * and - infinity, as cases of the `TVInt` enum.
 *
 * There are two helpers defined for `TVInt`: `minOf` returns the minimum of a `TVInt` object w.r.t. an `Int`,
 * and `maxOf` returns the maximum. This is in turn used in the `lowerBound` and `upperBound` helper methods
 * we defined as extension methods on the a `Set[Interval]` concrete domain, which gives us the lower
 * and upper bounds of the set of integers, correspondingly.
 */
object IntervalDomain {
  case class Interval(lower: Option[Int], upper: Option[Int]) {
    def isBottom: Boolean = lower.isDefined && upper.isDefined && lower.get > upper.get
  }

  given IntervalDomain: AbstractDomain[Interval] with {
    override def zero: Interval = Interval(Some(1), Some(0)) // Bottom: inconsistent interval

    override def one: Interval = Interval(None, None) // Top: [-∞, +∞]

    override def join(x: Interval, y: Interval): Interval = {
      if (x.isBottom) y
      else if (y.isBottom) x
      else Interval(
        (x.lower, y.lower) match {
          case (None, _) | (_, None) => None
          case (Some(a), Some(b)) => Some(a.min(b))
        },
        (x.upper, y.upper) match {
          case (None, _) | (_, None) => None
          case (Some(a), Some(b)) => Some(a.max(b))
        }
      )
    }

    override def meet(x: Interval, y: Interval): Interval = {
      val newLower = (x.lower, y.lower) match {
        case (None, b) => b
        case (a, None) => a
        case (Some(a), Some(b)) => Some(a.max(b))
      }
      val newUpper = (x.upper, y.upper) match {
        case (None, b) => b
        case (a, None) => a
        case (Some(a), Some(b)) => Some(a.min(b))
      }
      Interval(newLower, newUpper)
    }

    override def widen(x: Interval, y: Interval): Interval = {
      if (x.isBottom) y
      else if (y.isBottom) x
      else Interval(
        (x.lower, y.lower) match {
          case (Some(a), Some(b)) if b < a => None // Widen to -∞
          case _ => x.lower
        },
        (x.upper, y.upper) match {
          case (Some(a), Some(b)) if b > a => None // Widen to +∞
          case _ => x.upper
        }
      )
    }
  }

  enum TVInt {
    case PlusInf()
    case MinusInf()
    case Integer(i: Int)

    def minOf(x: Int) : TVInt = {
      this match {
        case PlusInf() => Integer(x)
        case MinusInf() => MinusInf()
        case Integer(i) => Integer(i.min(x))
      }
    }

    def maxOf(x: Int) : TVInt = {
      this match {
        case PlusInf() => PlusInf()
        case MinusInf() => Integer(x)
        case Integer(i) => Integer(i.max(x))
      }
    }

    def get: Option[Int] =
      this match
        case PlusInf() | MinusInf() => None
        case Integer(i) => Some(i)
  }

  given AbstractDomain[Set[Interval]] with {

    override def zero: Set[Interval] = Set()

    override def one: Set[Interval] = Set(Interval(None, None))

    override def join(lhs: Set[Interval], rhs: Set[Interval]): Set[Interval] = lhs.union(rhs)

    override def meet(lhs: Set[Interval], rhs: Set[Interval]): Set[Interval] = lhs.intersect(rhs)
  }

  extension (a: Set[Interval]) {
    def lowerBound: TVInt =
      a.foldLeft(TVInt.PlusInf())(
        (currBest, x) =>
          x.lower match {
            case Some(l) => currBest.minOf(l)
            case None => TVInt.MinusInf()
          }
      )

    def upperBound: TVInt =
      a.foldLeft(TVInt.MinusInf())(
        (currBest, y) =>
          y.upper match {
            case Some(l) => currBest.maxOf(l)
            case None => TVInt.PlusInf()
          }
      )
  }

  // abstraction and concretization functions.
  given IntervalAbstraction: GaloisConnection[Set[Interval], Interval] with {
    override def abstraction(concrete: Set[Interval]): Interval = {
      if (concrete.isEmpty) Interval(Some(1), Some(0)) // Bottom
      else Interval(concrete.lowerBound.get, concrete.upperBound.get)
    }

    override def concretization(interval: Interval): Set[Interval] = {
      interval match {
        case Interval(Some(l), Some(u)) if l <= u => Set(interval)
        case Interval(None, Some(u)) => Set(interval) // Approximation of (-∞, u]
        case Interval(Some(l), None) => Set(interval) // Approximation of [l, +∞)
        case Interval(None, None) => Set(interval) // Approximation of all integers
        case _ => Set.empty // Bottom case
      }
    }
  }

}
