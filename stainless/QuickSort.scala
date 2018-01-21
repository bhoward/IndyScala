import stainless.proof._
import stainless.lang._
import stainless.collection._

object QuickSort {
  def isSorted(list: List[Int]): Boolean = {
    list match {
      case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
      case _ => true
    }
  }

  def appendSorted(l1: List[Int], l2: List[Int]): List[Int] = {
    require(isSorted(l1) && isSorted(l2) && (l1.isEmpty || l2.isEmpty || l1.last <= l2.head))

    l1 match {
      case Nil() => l2
      case Cons(x, xs) => Cons(x, appendSorted(xs, l2))
    }
  } ensuring { result =>
    isSorted(result) &&
    result.content == l1.content ++ l2.content
  }

  def quickSort(list: List[Int]): List[Int] = {
    decreases(list.size, BigInt(0))

    list match {
      case Nil() => Nil[Int]()
      case Cons(x, xs) => par(x, Nil(), Nil(), xs)
    }
  } ensuring { result =>
    isSorted(result) &&
    result.content == list.content
  }

  def par(x: Int, l: List[Int], r: List[Int], ls: List[Int]): List[Int] = {
    require(
      forall((a: Int) => l.contains(a) ==> a <= x) &&
      forall((a: Int) => r.contains(a) ==> x < a)
    )
    decreases(l.size + r.size + ls.size, ls.size + 1)

    ls match {
      case Nil() => appendSorted(quickSort(l), Cons(x, quickSort(r)))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  } ensuring { result =>
    isSorted(result) &&
    result.content == l.content ++ r.content ++ ls.content + x
  }
}
