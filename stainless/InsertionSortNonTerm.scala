import stainless.lang._
import stainless.collection._

object InsertionSort {
  def isSorted(l: List[Int]): Boolean = l match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }

  def insert(e: Int, l: List[Int]): List[Int] = {
    require(isSorted(l))

    l match {
      case Nil() => Cons(e, Nil())
      case Cons(x, xs) => if (x <= e) Cons(x, insert(e, xs)) else Cons(e, l)
    }
  } ensuring { result =>
    isSorted(result) &&
    result.content == l.content + e &&
    result.size == l.size + 1
  }

  def sort(l: List[Int]): List[Int] = {
    // This satisfies the verification conditions, but is trivially non-terminating:
    sort(l)
  } ensuring { result =>
    isSorted(result) &&
    result.content == l.content &&
    result.size == l.size
  }
}
