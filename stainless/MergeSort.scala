import stainless.lang._
import stainless.collection._

object MergeSort {
  def contents[T](list: List[T]): Bag[T] = list match {
    case Nil() => Bag.empty[T]
    case Cons(x, xs) => contents(xs) + x
  }

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, tail @ Cons(x2, _)) => x1 <= x2 && isSorted(tail)
    case _ => true
  }

  def merge(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x <= y) Cons(x, merge(xs, l2))
        else Cons(y, merge(l1, ys))
      case (Nil(), _) => l2
      case (_, Nil()) => l1
    }
  } ensuring { result =>
    isSorted(result) &&
    contents(result) == contents(l1) ++ contents(l2) &&
    result.size == l1.size + l2.size
  }

  def split(list: List[BigInt]): (List[BigInt], List[BigInt]) = {
    require(list.size > 1)
    list match {
      case Cons(x, xs) if xs.size <= 2 => // BTH: change 2 to 1 to catch a bug
        (List(x), xs)
      case Cons(x1, Cons(x2, xs)) =>
        val (s1, s2) = split(xs)
        (Cons(x1, s1), Cons(x2, s2))
    }
  } ensuring { result => result match {
    case (left, right) =>
      contents(left) ++ contents(right) == contents(list) &&
      left.size + right.size == list.size &&
      left.size > 0 &&
      right.size > 0
    }
  }

  def mergeSort(list: List[BigInt]): List[BigInt] = {
    list match {
      case Cons(_, Cons(_, _)) =>
        val (s1, s2) = split(list)
        merge(mergeSort(s1), mergeSort(s2))
      case _ => list
    }
  } ensuring { result =>
    isSorted(result) &&
    contents(result) == contents(list) &&
    result.size == list.size
  }
}
