import stainless.lang._
import stainless.collection._

object InsertionSort {
  def size[T](l: List[T]): BigInt = {
    l match {
      case Nil() => BigInt(0)
      case Cons(_, xs) => 1 + size(xs)
    }
  } ensuring(_ >= 0)

  def contents[T](l: List[T]): Bag[T] = l match {
    case Nil() => Bag.empty
    case Cons(x, xs) => contents(xs) + x
  }

  def isSorted(l: List[Int]): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs @ Cons(y, ys)) => x <= y && isSorted(xs)
  }

  def insert(e: Int, l: List[Int]): List[Int] = {
    require(isSorted(l))
    l match {
      case Nil() => Cons(e, Nil())
      case Cons(x, xs) => if (x <= e) Cons(x, insert(e, xs)) else Cons(e, l)
    }
  } ensuring {result =>
    contents(result) == contents(l) + e &&
      isSorted(result) &&
      size(result) == size(l) + 1
  }

  def sort(l: List[Int]): List[Int] = {
    l match {
      case Nil() => Nil[Int]()
      case Cons(x, xs) => insert(x, sort(xs))
    }
  } ensuring {result =>
    contents(result) == contents(l) &&
      isSorted(result) &&
      size(result) == size(l)
  }
}
