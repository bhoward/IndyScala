import stainless.lang._
import stainless.collection._

object InsertionSort {
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
    isSorted(result) &&
    result.content == l.content + e &&
    result.size == l.size + 1
  }

  def sort(l: List[Int]): List[Int] = {
    l match {
      case Nil() => Nil[Int]()
      case Cons(x, xs) => insert(x, sort(xs))
    }
  } ensuring {result =>
    isSorted(result) &&
    result.content == l.content &&
    result.size == l.size
  }
}
