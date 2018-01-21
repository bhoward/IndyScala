import stainless.lang._
import stainless.collection._

object SelectionSort {
  def isSorted(l: List[Int]): Boolean = l match {
    case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
    case _ => true
  }

  def select(l: List[Int]): (Int, List[Int]) = {
    require(l.size > 0)

    l match {
      case Cons(x, Nil()) => (x, Nil[Int]())
      case Cons(x, xs) =>
        val (min, rest) = select(xs)
        if (x <= min) (x, xs) else (min, Cons(x, rest))
    }
  } ensuring { result =>
    val (min, rest) = result
    forall((x: Int) => rest.contains(x) ==> min <= x) &&
    l.content == rest.content + min &&
    l.size == rest.size + 1
  }

  def sort(l: List[Int]): List[Int] = {
    decreases(l.size)

    l match {
      case Nil() => Nil[Int]()
      case _ =>
        val (min, rest) = select(l)
        Cons(min, sort(rest))
    }
  } ensuring {result =>
    isSorted(result) &&
    result.content == l.content &&
    result.size == l.size
  }
}
