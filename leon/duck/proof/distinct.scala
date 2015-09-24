package duck.proof

import duck.collection.List._
import leon.annotation._
import leon.lang._
import leon.proof._
import DeleteSpec._
import DeleteOps._
import DistinctSpec._
import DistinctOps._
import DistinctLemmas._

import scala.language.postfixOps

@library
object DistinctSpec {
  @induct
  def distinct_delete[V] (list: List[V], e: V): Boolean = {
    require(distinct(list))
    distinct(delete(list, e))
  } holds

  @induct
  def distinct_cons_not_contains[V] (list: List[V], e: V): Boolean = {
    require(distinct(list) && !list.contains(e))
    distinct(e :: list)
  } holds

  def distinct_delete_content[V] (l1: List[V], l2: List[V], e: V): Boolean = {
    require(distinct(l1) && distinct(l2) && l1.content == l2.content)
    delete(l1, e).content == delete(l2, e).content because
      distinct_delete_content_lemma(l1, l2, e)
  } holds
}

@library
object DistinctOps {
  /**
   * Tell whether a list contains no duplicate elements.
   * @param list a list
   * @return whether list contains no duplicate elements
   */
  def distinct[V] (list: List[V]): Boolean = {
    if (list == Nil[V]()) trivial
    else !list.tail.contains(list.head) && distinct(list.tail)
  }
}

@library
object DistinctLemmas {
  @induct
  def distinct_sublist_lemma[V] (l1: List[V], l2: List[V]): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1) && distinct(l2)
  } holds /* verified by Leon */

  @induct
  def distinct_excl_lemma[V] (l1: List[V], l2: List[V], m: V): Boolean = {
    require(distinct(l1 ++ l2) && l2.contains(m))
    !l1.contains(m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma1[V] (l1: List[V], l2: List[V], m: V): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(delete(l1, m) ++ l2) because distinct_delete_lemma3(l1, m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma2[V] (l1: List[V], l2: List[V], m: V): Boolean = {
    require(distinct(l1 ++ l2))
    distinct(l1 ++ delete(l2, m)) because distinct_delete_lemma3(l2, m)
  } holds /* verified by Leon */

  @induct
  def distinct_delete_lemma3[V] (list: List[V], m: V): Boolean = {
    !distinct(list) || distinct(delete(list, m))
  } holds /* verified by Leon */

  @induct
  def distinct_delete_content0[V] (list: List[V], e: V): Boolean = {
    require(distinct(list) && (list contains e))
    val L = delete(list, e)
    L.content == list.content -- Set(e) && distinct(L)
  } holds

  @induct
  def distinct_delete_content_lemma[V] (l1: List[V], l2: List[V], e: V): Boolean = {
    require(distinct(l1) && distinct(l2) && l1.content == l2.content)
    val L1 = delete(l1, e)
    val L2 = delete(l2, e)
    if (l1 contains e) {
      L1.content == L2.content && distinct(L1) && distinct(L2) because {
        check {
          distinct_delete_content0(l1, e) && distinct_delete_content0(l2, e)
        }
      }
    } else {
      L1.content == L2.content && distinct(L1) && distinct(L2) because {
        check { delete_not_contains(l1, e) && delete_not_contains(l2, e) }
      }
    }
  } holds
}
