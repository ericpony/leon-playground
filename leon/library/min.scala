import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import MinOps._
import MinLemmas._
import scala.language.postfixOps

object MinSpec {
  @induct
  def min_contains (list : List[BigInt], m : BigInt) : Boolean = {
    require (list contains m)
    min (list) <= m
  } holds

  def min_content (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (l1.content == l2.content && l1 != Nil[BigInt]())
    min (l1) == min (l2) because
      check { min_contains (l1, min (l2)) } &&
      check { min_contains (l2, min (l1)) }
  } holds
}

object MinOps {
  /**
   * Obtain the minimal element of the input list.
   * @param list a list
   * @return the minimal element of the input list
   */
  def min (list: List[BigInt]): BigInt = {
    require(list != Nil[BigInt]())
    list match {
      case Cons(x, xs) =>
        if (xs == Nil[BigInt]()) x
        else min(x, min(xs))
    }
  } ensuring {
    res => (list contains res) &&
      list.forall(res <= _) because min_lemma(list, res)
  } /* verified by Leon */

  def min (x: BigInt, y: BigInt) = if (x < y) x else y
}

object MinLemmas {
  @induct
  def min_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(list != Nil[BigInt]())
    m > min(list) || list.forall(m <= _)
  } holds /* verified by Leon */

  /* Check that min(list) is indeed the minimal element of list. */
  def min_lemma2 (list: List[BigInt]): Boolean = {
    require(list != Nil[BigInt]())
    val m = min(list)
    list.contains(m) && list.forall(m <= _) because min_lemma(list, m)
  } holds /* verified by Leon */

  /**
   * Check that min(l1 ++ l2) == min(l2 ++ l1).
   */
  def min_concat_lemma (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l2 == Nil[BigInt]() ||
      l1 == Nil[BigInt]() || {
      min(l1 ++ l2) == min(l2 ++ l1) because {
        min(l1 ++ l2) == min(min(l1), min(l2)) && min_concat_lemma2(l1, l2) &&
          min(l2 ++ l1) == min(min(l2), min(l1)) && min_concat_lemma2(l2, l1) &&
          min(min(l1), min(l2)) == min(min(l2), min(l1))
      }
    }
  } holds /* verified by Leon */

  /**
   * Check that min(l1 ++ l2) == min(min(l1), min(l2)).
   */
  @induct
  def min_concat_lemma2 (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l2 == Nil[BigInt]() ||
      l1 == Nil[BigInt]() ||
      min(l1 ++ l2) == min(min(l1), min(l2))
  } holds /* verified by Leon */

  @induct
  def min_contains (list : List[BigInt], m : BigInt) : Boolean = {
    require (list contains m)
    min (list) <= m
  } holds
}
