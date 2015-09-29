package duck.spec

import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._
import ListOps._

@library
object ListSpec {
  /* see SortedListSpec and DistinctSortedListSpec */
}

@library
object ListLemmas {
  def snocIndex[T] (l: List[T], t: T, i: BigInt): Boolean = {
    require(0 <= i && i < l.size + 1)
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t)) because
      (l match {
        case Nil()       => true
        case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
      })
  }.holds

  def reverseIndex[T] (l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil()       => true
      case Cons(x, xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
      (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def snocLast[T] (l: List[T], x: T): Boolean = {
    ((l :+ x).last == x) because {
      l match {
        case Nil()       => true
        case Cons(y, ys) => {
          ((y :: ys) :+ x).last ==| trivial |
            (y :: (ys :+ x)).last ==| trivial |
            (ys :+ x).last ==| snocLast(ys, x) |
            x
        }.qed
      }
    }
  }.holds

  def headReverseLast[T] (l: List[T]): Boolean = {
    require(!l.isEmpty)
    (l.head == l.reverse.last) because {
      (l: @unchecked) match {
        case Cons(x, xs) => {
          (x :: xs).head ==| trivial |
            x ==| snocLast(xs.reverse, x) |
            (xs.reverse :+ x).last ==| trivial |
            (x :: xs).reverse.last
        }.qed
      }
    }
  }.holds

  def appendIndex[T] (l1: List[T], l2: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size))) because {
      l1 match {
        case Nil()       => true
        case Cons(x, xs) =>
          (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
      }
    }
  }.holds

  @induct
  def appendAssoc[T] (l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  @induct
  def rightUnitAppend[T] (l1: List[T]): Boolean = {
    l1 ++ Nil() == l1
  }.holds

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  def leftUnitAppend[T] (l1: List[T]): Boolean = {
    Nil() ++ l1 == l1
  }.holds

  def snocIsAppend[T] (l: List[T], t: T): Boolean = {
    ((l :+ t) == l ++ Cons[T](t, Nil())) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => snocIsAppend(xs, t)
      }
    }
  }.holds

  def snocAfterAppend[T] (l1: List[T], l2: List[T], t: T): Boolean = {
    ((l1 ++ l2) :+ t == l1 ++ (l2 :+ t)) because {
      l1 match {
        case Nil()       => true
        case Cons(x, xs) => snocAfterAppend(xs, l2, t)
      }
    }
  }.holds

  def snocReverse[T] (l: List[T], t: T): Boolean = {
    ((l :+ t).reverse == Cons(t, l.reverse)) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => snocReverse(xs, t)
      }
    }
  }.holds

  def reverseReverse[T] (l: List[T]): Boolean = {
    l.reverse.reverse == l because {
      l match {
        case Nil()       => trivial
        case Cons(x, xs) => {
          (xs.reverse :+ x).reverse ==| snocReverse[T](xs.reverse, x) |
            x :: xs.reverse.reverse ==| reverseReverse[T](xs) |
            (x :: xs)
        }.qed
      }
    }
  }.holds

  def reverseAppend[T] (l1: List[T], l2: List[T]): Boolean = {
    ((l1 ++ l2).reverse == l2.reverse ++ l1.reverse) because {
      l1 match {
        case Nil()       => {
          (Nil() ++ l2).reverse ==| trivial |
            l2.reverse ==| rightUnitAppend(l2.reverse) |
            l2.reverse ++ Nil() ==| trivial |
            l2.reverse ++ Nil().reverse
        }.qed
        case Cons(x, xs) => {
          ((x :: xs) ++ l2).reverse ==| trivial |
            (x :: (xs ++ l2)).reverse ==| trivial |
            (xs ++ l2).reverse :+ x ==| reverseAppend(xs, l2) |
            (l2.reverse ++ xs.reverse) :+ x ==|
              snocAfterAppend(l2.reverse, xs.reverse, x) |
            l2.reverse ++ (xs.reverse :+ x) ==| trivial |
            l2.reverse ++ (x :: xs).reverse
        }.qed
      }
    }
  }.holds

  def snocFoldRight[A, B] (xs: List[A], y: A, z: B, f: (A, B) => B): Boolean = {
    ((xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f)) because {
      xs match {
        case Nil()       => true
        case Cons(x, xs) => snocFoldRight(xs, y, z, f)
      }
    }
  }.holds

  def folds[A, B] (xs: List[A], z: B, f: (B, A) => B): Boolean = {
    val f2 = (x: A, z: B) => f(z, x)
    (xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2)) because {
      xs match {
        case Nil()       => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(f) ==| trivial |
            xs.foldLeft(f(z, x))(f) ==| folds(xs, f(z, x), f) |
            xs.reverse.foldRight(f(z, x))(f2) ==| trivial |
            xs.reverse.foldRight(f2(x, z))(f2) ==|
              snocFoldRight(xs.reverse, x, z, f2) |
            (xs.reverse :+ x).foldRight(z)(f2) ==| trivial |
            (x :: xs).reverse.foldRight(z)(f2)
        }.qed
      }
    }
  }.holds

  def scanVsFoldLeft[A, B] (l: List[A], z: B, f: (B, A) => B): Boolean = {
    (l.scanLeft(z)(f).last == l.foldLeft(z)(f)) because {
      l match {
        case Nil()       => true
        case Cons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
      }
    }
  }.holds

  //// my hand calculation shows this should work, but it does not seem to be found
  //def associative[T,U](l1: List[T], l2: List[T], f: List[T] => U, op: (U,U) => U) = {
  //  f(l1 ++ l2) == op(f(l1), f(l2))
  //}
  //
  //def existsAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
  //  associative[T, Boolean](l1, l2, _.exists(p), _ || _ )
  //}.holds
  //
  //def forallAssoc[T](l1: List[T], l2: List[T], p: T => Boolean) = {
  //  associative[T, Boolean](l1, l2, _.exists(p), _ && _ )
  //}.holds

  @induct
  def scanVsFoldRight[A, B] (l: List[A], z: B, f: (A, B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A] (l1: List[A], l2: List[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T] (ls: List[List[T]]): Boolean = {
    val f: (List[T], Set[T]) => Set[T] = _.content ++ _
    (flatten(ls).content == ls.foldRight(Set[T]())(f)) because {
      ls match {
        case Nil()      => true
        case Cons(h, t) => {
          flatten(h :: t).content ==| trivial |
            (h ++ flatten(t)).content ==| appendContent(h, flatten(t)) |
            h.content ++ flatten(t).content ==| flattenPreservesContent(t) |
            h.content ++ t.foldRight(Set[T]())(f) ==| trivial |
            f(h, Set[T]()) ++ t.foldRight(Set[T]())(f) ==| trivial |
            (h :: t).foldRight(Set[T]())(f)
        }.qed
      }
    }
  }.holds

  // A lemma about `append` and `updated`
  def appendUpdate[T] (l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    // induction scheme
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).updated(i, y) == (
        if (i < l1.size)
          l1.updated(i, y) ++ l2
        else
          l1 ++ l2.updated(i - l1.size, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T] (l1: List[T], l2: List[T], n: BigInt): Boolean = {
    //induction scheme
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }) &&
      // lemma
      ((l1 ++ l2).take(n) == (
        if (n < l1.size) l1.take(n)
        else if (n > l1.size) l1 ++ l2.take(n - l1.size)
        else l1)) &&
      ((l1 ++ l2).drop(n) == (
        if (n < l1.size) l1.drop(n) ++ l2
        else if (n > l1.size) l2.drop(n - l1.size)
        else l2))
  }.holds

  // A lemma about `append` and `insertAt`
  def appendInsert[T] (l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      ((l1 ++ l2).insertAt(i, y) == (
        if (i < l1.size) l1.insertAt(i, y) ++ l2
        else l1 ++ l2.insertAt((i - l1.size), y)))
  }.holds

}

