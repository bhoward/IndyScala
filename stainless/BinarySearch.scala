import stainless.lang._

object BinarySearch {
  def exists[T](p: T => Boolean): Boolean = !forall((t: T) => !p(t))

  def isSorted(arr: Array[Int]): Boolean = {
    forall((i: Int, j: Int) => (0 <= i && i < j && j < arr.length) ==> arr(i) <= arr(j))
  }

  def search(arr: Array[Int], x: Int, lo: Int, hi: Int): Boolean = {
    require(0 <= lo && lo <= hi+1 && hi < arr.length && isSorted(arr))
    decreases(hi - lo + 1)

    if (lo <= hi) {
      val i = lo + (hi - lo) / 2
      val y = arr(i)
      if (x == y) true
      else if (x < y) search(arr, x, lo, i-1)
      else search(arr, x, i+1, hi)
    } else {
      false
    }
  } ensuring { result =>
    result == exists((i: Int) => lo <= i && i <= hi && arr(i) == x)
  }
}
