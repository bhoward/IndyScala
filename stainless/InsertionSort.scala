import stainless.lang._

object InsertionSort {
  sealed trait List

  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List): BigInt = ({
    l match {
      case Nil => BigInt(0)
      case Cons(_, xs) => 1 + size(xs)
    }
  }) ensuring(_ >= 0)

  def contents(l: List): Set[Int] = l match {
    case Nil => Set.empty
    case Cons(x, xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil => true
    case Cons(x, Nil) => true
    case Cons(x, xs @ Cons(y, ys)) => x <= y && isSorted(xs)
  }

  def insert(e: Int, l: List): List = ({
    require(isSorted(l))
    l match {
      case Nil => Cons(e, Nil)
      case Cons(x, xs) => if (x <= e) Cons(x, insert(e, xs)) else Cons(e, l)
    }
  }) ensuring {result =>
    contents(result) == contents(l) ++ Set(e) &&
      isSorted(result) &&
      size(result) == size(l) + 1
  }

  def sort(l: List): List = {
    l match {
      case Nil => Nil
      case Cons(x, xs) => insert(x, sort(xs))
    }
  } ensuring {result =>
    contents(result) == contents(l) &&
      isSorted(result) &&
      size(result) == size(l)
  }
}
