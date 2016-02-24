import duck.collection._
import leon.lang._
import leon.proof._
import leon.annotation._
import scala.language.{implicitConversions, postfixOps}
import PigeonHolePrinciples._
import PigeonHolePrinciplesLemmas._

object PigeonHolePrinciples {

  def sum (a : List[BigInt]) : BigInt = a.foldRight(BigInt(0))(_ + _)

  def hasCollision (a : List[BigInt]) : Boolean = {
    a match {
      case Nil()  => false
      case h :: t => t.contains(h) || hasCollision(t)
    }
  }

  def pigeonhole_principle (a : List[BigInt], n : BigInt) : Boolean = {
    require(n == a.length && a.length >= 2 && boundedBy(a, 0, n))
    hasCollision(a) because {
      if (a.length == 2) {
        trivial
      } else {
        if (count(a, n - 1) >= 2) {
          pigeon_lemma_1(a, n - 1)
        } else if (count(a, n - 1) == 0) {
          pigeon_lemma_3(a, n - 1) &&
            pigeon_lemma_2(a, n) &&
            pigeonhole_principle(a.tail, n - 1) &&
            pigeon_lemma_5(a, a.head, n)
        } else {
          // count(a, n - 1) == 1
          val a2 = a.removeFirst(n - 1)
          pigeon_lemma_4(a, n) &&
            pigeonhole_principle(a2, n - 1) &&
            pigeon_lemma_5(a, n - 1, n)
        }
      }
    }
  } holds /* verified */

  def pigeonhole_principle_array (a : Array[Int]) : Boolean = {
    require(forall((i : Int) =>
      ArrayOps(a).isDefinedAt(i) ==> boundedBy(a(i), 0, a.length))
    )
    exists((i : Int, j : Int) =>
      (ArrayOps(a).isDefinedAt(i) && ArrayOps(a).isDefinedAt(j) && i != j) ==> (a(i) == a(j))
    )
  } holds /* verified */

  @induct
  def pigeonhole_principle_v2 (a : List[BigInt]) : Boolean = {
    require(a.forall(ai => ai >= 0 && ai <= 1))
    sum(a) <= a.size
  } holds /* verified */

  @induct
  def pigeonhole_principle_v3 (a : List[BigInt]) : Boolean = {
    require(sum(a) > a.size && a.forall(_ >= 0))
    a.exists(_ > 1)
  } holds /* verified */
}

object PigeonHolePrinciplesLemmas {

  case class ArrayOps[T] (a : Array[T]) {
    def isDefinedAt (i : Int) = 0 <= i && i < a.length
  }

  /* Leon cannot handle implicit conversion with type parameter */
  //implicit def extendedArray[T] (a : Array[T]) = ArrayOps[T](a)

  def exists[A] (p : A => Boolean) : Boolean = !forall((x : A) => !p(x))
  def exists[A, B] (p : (A, B) => Boolean) : Boolean = !forall((x : A, y : B) => !p(x, y))

  def boundedBy (i : Int, lower : Int, upper : Int) = lower < i && i < upper
  def boundedBy (i : BigInt, lower : BigInt, upper : BigInt) = lower < i && i < upper
  def boundedBy (a : List[BigInt], lower : BigInt, upper : BigInt) : Boolean = {
    a match {
      case Nil()  => true
      case h :: t => (lower < h && h < upper) && boundedBy(t, lower, upper)
    }
  }

  def not_eq (a : List[BigInt], e : BigInt) : Boolean = {
    a match {
      case Nil()  => true
      case h :: t => (h != e) && not_eq(t, e)
    }
  }

  def eq (a : List[BigInt], e : BigInt) : Boolean = {
    a match {
      case Nil()  => true
      case h :: t => (h == e) && eq(t, e)
    }
  }

  /**
    * We need to put this function in the post-condition of `count`,
    * so that Leon can identify the result of `count` with the number
    * of the counted elements in the provided list.
    */
  def sublist_eq (a : List[BigInt], e : BigInt) : List[BigInt] = {
    a match {
      case Nil()  => a
      case h :: t => if (h == e) h :: sublist_eq(t, e) else sublist_eq(t, e)
    }
  }

  def count (a : List[BigInt], e : BigInt) : BigInt = {
    a match {
      case Nil()  => BigInt(0)
      case h :: t => if (h == e) BigInt(1) + count(t, e) else BigInt(0) + count(t, e)
    }
  } ensuring { res =>
    res == sublist_eq(a, e).length &&
      /* Without the above assertion, Leon can only prove (res > 0) ==> a.contains(e). */
      (res > 0) == a.contains(e)
  } /* verified */

  @induct
  def forall_conjunct (a : List[BigInt], p : BigInt => Boolean, q : BigInt => Boolean) : Boolean = {
    require(a.forall(p) && a.forall(q))
    a.forall(ai => p(ai) && q(ai))
  } holds /* verified */

  @induct
  def can_loosen_upperbound (a : List[BigInt], lower : BigInt, upper : BigInt) : Boolean = {
    require(boundedBy(a, 0, upper))
    boundedBy(a, 0, upper + 1)
  } holds /* verified */

  @induct
  def can_tighten_upperbound (a : List[BigInt], lower : BigInt, upper : BigInt) : Boolean = {
    require(boundedBy(a, lower, upper) && not_eq(a, upper - 1))
    boundedBy(a, lower, upper - 1)
  } holds

  @induct
  def pigeon_lemma_2 (a : List[BigInt], n : BigInt) : Boolean = {
    (boundedBy(a, 0, n) && not_eq(a, n - 1)) ==>
      boundedBy(a, 0, n - 1)
  } holds /* verified */

  @induct
  def pigeon_lemma_1 (a : List[BigInt], n : BigInt) : Boolean = {
    require(count(a, n) >= 2)
    hasCollision(a)
  } holds /* verified */

  @induct
  def pigeon_lemma_3 (a : List[BigInt], n : BigInt) : Boolean = {
    require(count(a, n) == 0)
    not_eq(a, n)
  } holds /* verified */

  @induct
  def pigeon_lemma_4 (a : List[BigInt], n : BigInt) : Boolean = {
    require(count(a, n - 1) == 1 && boundedBy(a, 0, n))
    val a2 = a.removeFirst(n - 1)
    boundedBy(a2, 0, n - 1) because {
      if (a.head != n - 1) {
        trivial
      } else {
        pigeon_lemma_3(a2, n - 1) &&
          can_tighten_upperbound(a2, 0, n)
      }
    }
  } holds /* verified */

  @induct
  def pigeon_lemma_5 (a : List[BigInt], e : BigInt, n : BigInt) : Boolean = {
    require(n == a.length && a.length >= 2 && boundedBy(a.removeFirst(e), 0, n - 1) &&
      a.contains(e) &&
      boundedBy(e, 0, n) &&
      pigeonhole_principle(a.removeFirst(e), n - 1))
    pigeon_lemma_5_1(a, e, n) &&
      pigeonhole_principle(a, n)
  } holds /* verified */

  @induct
  def pigeon_lemma_5_1 (a : List[BigInt], e : BigInt, n : BigInt) : Boolean = {
    require(boundedBy(a.removeFirst(e), 0, n - 1) &&
      a.contains(e) &&
      0 < e && e < n)
    boundedBy(a, 0, n) because {
      if (a.head != e) {
        trivial
      } else {
        can_loosen_upperbound(a.tail, 0, n - 1)
      }
    }
  } holds /* verified */
}
