import duck.collection._
import leon.lang._
import leon.proof._
import leon.annotation._
import scala.language.{implicitConversions, postfixOps}
import PigeonHolePrinciples._
import PigeonHolePrinciplesLemmas._

object PigeonHolePrinciples {

  def sum (a : List[BigInt]) : BigInt = a.foldRight(BigInt(0))(_ + _)

  def has_collision (a : List[BigInt]) : Boolean = {
    a match {
      case Nil()  => false
      case h :: t => t.contains(h) || has_collision(t)
    }
  }

  def pigeonhole_principle (a : List[BigInt]) : Boolean = {
    require(a.length >= 2 && bounded_by(a, 0, a.length))
    has_collision(a) because {
      if (a.length == BigInt(2)) {
        trivial
      } else {
        frequency_of(a, a.length - 1) match {
          case BigInt(1) =>
            pigeon_lemma_2(a, a.length) &&
              pigeon_lemma_3(a, a.length - 1, a.length) &&
              pigeonhole_principle(a.removeFirst(a.length - 1))
          case BigInt(0) =>
            can_tighten_upperbound(a, 0, a.length) &&
              pigeon_lemma_3(a, a.head, a.length) &&
              pigeonhole_principle(a.tail)
          case _         =>
            pigeon_lemma_1(a, a.length - 1)
        }
      }
    }
  } holds /* verified */

  def pigeonhole_principle (a : Array[Int]) : Boolean = {
    require(forall((i : Int) =>
      ArrayOps(a).is_defined_at(i) ==> bounded_by(a(i), 0, a.length))
    )
    exists((i : Int, j : Int) =>
      (ArrayOps(a).is_defined_at(i, j) && i != j) ==> (a(i) == a(j))
    )
  } holds /* verified */

  @induct
  def pigeonhole_principle_v2 (a : List[BigInt]) : Boolean = {
    require(a.forall(between(_, 0, 1)))
    between(sum(a), 0, a.length)
  } holds /* verified */

  @induct
  def pigeonhole_principle_v3 (a : List[BigInt]) : Boolean = {
    require(sum(a) > a.size && a.forall(_ >= 0))
    a.exists(_ > 1)
  } holds /* verified */
}

object PigeonHolePrinciplesLemmas {

  case class ArrayOps[T] (a : Array[T]) {
    def is_defined_at (i : Int) : Boolean = 0 <= i && i < a.length
    def is_defined_at (i : Int, j : Int) : Boolean = is_defined_at(i) && is_defined_at(j)
  }

  /* Leon cannot handle implicit conversion with type parameter */
  //implicit def extendedArray[T] (a : Array[T]) = ArrayOps[T](a)

  def exists[A] (p : A => Boolean) : Boolean = !forall((x : A) => !p(x))
  def exists[A, B] (p : (A, B) => Boolean) : Boolean = !forall((x : A, y : B) => !p(x, y))

  def bounded_by (i : Int, lower : Int, upper : Int) = lower < i && i < upper
  def bounded_by (i : BigInt, lower : BigInt, upper : BigInt) = lower < i && i < upper
  def bounded_by (a : List[BigInt], lower : BigInt, upper : BigInt) : Boolean = {
    a.forall(bounded_by(_, lower, upper))
  }
  def between (i : BigInt, min : BigInt, max : BigInt) = min <= i && i <= max

  def frequency_of (a : List[BigInt], e : BigInt) : BigInt = {
    a match {
      case Nil()  => BigInt(0)
      case h :: t => if (h == e) BigInt(1) + frequency_of(t, e) else BigInt(0) + frequency_of(t, e)
    }
  } ensuring { res =>
    /* The following assertion helps Leon identify the result of
       frequency_of with the number of the counted elements in the list. */
    res == a.filter(_ == e).length &&
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
    require(bounded_by(a, 0, upper))
    bounded_by(a, 0, upper + 1)
  } holds /* verified */

  @induct
  def can_tighten_upperbound (a : List[BigInt], lower : BigInt, upper : BigInt) : Boolean = {
    require(bounded_by(a, lower, upper) && !a.contains(upper - 1))
    bounded_by(a, lower, upper - 1)
  } holds

  @induct
  def pigeon_lemma_1 (a : List[BigInt], n : BigInt) : Boolean = {
    require(frequency_of(a, n) >= 2)
    has_collision(a)
  } holds /* verified */

  @induct
  def pigeon_lemma_2 (a : List[BigInt], n : BigInt) : Boolean = {
    require(frequency_of(a, n - 1) == BigInt(1) && bounded_by(a, 0, n))
    val a2 = a.removeFirst(n - 1)
    bounded_by(a2, 0, n - 1) because {
      if (a.head != n - 1) {
        trivial
      } else {
        can_tighten_upperbound(a2, 0, n)
      }
    }
  } holds /* verified */

  @induct
  def pigeon_lemma_3 (a : List[BigInt], e : BigInt, n : BigInt) : Boolean = {
    require(n == a.length && a.length >= 2 && bounded_by(a.removeFirst(e), 0, n - 1) &&
      a.contains(e) &&
      bounded_by(e, 0, n) &&
      pigeonhole_principle(a.removeFirst(e)))
    pigeon_lemma_3_1(a, e, n) &&
      pigeonhole_principle(a)
  } holds /* verified */

  @induct
  def pigeon_lemma_3_1 (a : List[BigInt], e : BigInt, n : BigInt) : Boolean = {
    require(bounded_by(a.removeFirst(e), 0, n - 1) &&
      a.contains(e) &&
      bounded_by(e, 0, n))
    bounded_by(a, 0, n) because {
      if (a.head != e) {
        trivial
      } else {
        can_loosen_upperbound(a.tail, 0, n - 1)
      }
    }
  } holds /* verified */
}
