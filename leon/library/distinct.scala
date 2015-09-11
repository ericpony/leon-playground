import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import DeleteSpec._
import DeleteOps._
import DistinctSpec._
import DistinctOps._
import DistinctLemmas._
import scala.language.postfixOps

object DistinctSpec {
}

object DistinctOps {
  /**
   * Tell whether a list contains no duplicate elements.
   * @param list a list
   * @return whether list contains no duplicate elements
   */
  def distinct (list: List[BigInt]): Boolean = {
    if (list == List[BigInt]()) trivial
    else !list.tail.contains(list.head) && distinct(list.tail)
  }
}

object DistinctLemmas {
  @induct
  def distinct_sublist_lemma (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1) && distinct(l2)
  } holds /* verified by Leon */

  @induct
  def distinct_excl_lemma (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2) && l2.contains(m))
    !l1.contains(m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma1 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(delete(l1, m) ++ l2) because distinct_delete_lemma3(l1, m)

  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma2 (l1: List[BigInt], l2: List[BigInt], m: BigInt): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1 ++ delete(l2, m)) because distinct_delete_lemma3(l2, m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma3 (list: List[BigInt], m: BigInt): Boolean = {
    !distinct(list) || distinct(delete(list, m))
  } holds /* verified by Leon */

  @induct
  def distinct_delete_content0 (list : List[BigInt], e : BigInt) : Boolean = {
    require (distinct (list) && (list contains e))
    val L = delete (list, e)
    L.content == list.content -- Set (e) && distinct (L)
  } holds

  @induct
  def distinct_delete_content (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require (distinct (l1) && distinct (l2) && l1.content == l2.content)
    val L1 = delete (l1, e)
    val L2 = delete (l2, e)
    if (l1 contains e) {
      L1.content == L2.content && distinct (L1) && distinct (L2) because {
        check { 
          distinct_delete_content0 (l1, e) && distinct_delete_content0 (l2, e)
        }
      }
    } else {
      L1.content == L2.content && distinct (L1) && distinct (L2) because {
        check { delete_not_contains (l1, e) && delete_not_contains (l2, e) }
      }
    }
  } holds
}
