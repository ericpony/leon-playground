package duck.spec

import duck.collection._
import duck.spec.SortedListOps._
import duck.spec.LeftistHeapLemmas._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.PermutationSpec._
import duck.proof.MinOps._
import duck.proof.DeleteOps._

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

/**
 * Bisimulation between LeftistHeap and List
 */
object Heap_List_BisimulationSpec {
  implicit def asHeap (l: List[BigInt]) = HeapADT(l)

  /**
   * h ~ l implies h.insert(e) ~ l.insert(e)
   */
  def bisim_insert (h: Heap, l: List[BigInt], e: BigInt): Boolean = {
    require(h.isHeap && h ~ l)
    h.insert(e) ~ l.insert(e) because {
      val L1 = h.insert(e)
      val L2 = l.insert(e)
      heap_insert_lemma(h, e) &&
        permutation_cons(h, l, e) &&
        permutation_eq(e :: l, L2) &&
        permutation_tran_lemma(L1, e :: h, e :: l) &&
        permutation_tran_lemma(L1, e :: l, L2)
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ l1 and h2 ~ l2 implies h1.merge(h2) ~ l1.merge(l2)
   */
  def bisim_merge (h1: Heap, h2: Heap, l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(h1.isHeap && h2.isHeap && h1 ~ l1 && h2 ~ l2)
    h1.merge(h2) ~ l1.merge(l2) because {
      val L1 = h1.merge(h2)
      val L2 = l1.merge(l2)
      heap_merge_lemma(h1, h2) &&
        permutation_append(h1, l1, h2) &&
        permutation_prepend(l1, l2, h2) &&
        permutation_tran(h1 ++ h2, l1 ++ h2, l1 ++ l2) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, l1.merge(l2))
    }
  } holds /* verified by Leon */

  /**
   * h ~ l implies h.findMin == l.findMin
   */
  def bisim_findMin (h: Heap, l: List[BigInt]): Boolean = {
    require(h.isHeap && h ~ l)
    h.findMin == l.findMin because {
      if (h == Empty())
        trivial
      else {
        findMin_lemma(h) &&
          min_permutation(h, l)
      }
    }
  } holds /* verified by Leon */

  /**
   * h ~ l implies h.deleteMin ~ l.deleteMin
   */
  def bisim_deleteMin (h: Heap, l: List[BigInt]): Boolean = {
    require(h.isHeap && h ~ l)
    h.deleteMin ~ l.deleteMin because {
      if (h == Empty())
        trivial
      else {
        bisim_deleteMin(h, l) &&
          permutation_delete(h, l, h.findMin.get)
      }
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ h2 implies h1.size == h2.size
   */
  def bisim_size (h: Heap, l: List[BigInt]): Boolean = {
    require(h.isHeap && h ~ l)
    h.size == l.size
  } holds /* verified by Leon */

  @induct
  def list_insert_comm_prop (l: List[BigInt], e1: BigInt, e2: BigInt) = {
    l.insert(e1).insert(e2) ~ l.insert(e2).insert(e1)
  } holds /* verified by Leon */

  def list_merge_comm_prop (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    l1.merge(l2) ~ l2.merge(l1) because
      permutation_concat_comm(l1, l2)
  } holds /* verified by Leon */

  def list_merge_assoc_prop (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]): Boolean = {
    l1.merge(l2).merge(l3) ~ l1.merge(l2.merge(l3)) because
      permutation_concat_assoc(l1, l2, l3)
  } holds /* verified by Leon */

  /**
   * h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1)
   */
  def heap_insert_comm_prop (h: Heap, e1: BigInt, e2: BigInt): Boolean = {
    require(h.isHeap)
    h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1) because {
      bisim_insert(h, h, e1) &&
        bisim_insert(h.insert(e1), e1 :: h, e2) &&
        list_insert_comm_prop(h, e1, e2) &&
        permutation_tran(
          h.insert(e1).insert(e2),
          e2 :: e1 :: h,
          e1 :: e2 :: h
        ) &&
        heap_insert_lemma(h, e2) &&
        permutation_cons(h.insert(e2), e2 :: h, e1) &&
        heap_insert_lemma(h.insert(e2), e1) &&
        permutation_tran(
          h.insert(e2).insert(e1),
          e1 :: h.insert(e2),
          e1 :: e2 :: h
        ) &&
        permutation_tran(
          h.insert(e1).insert(e2),
          e1 :: e2 :: h,
          h.insert(e2).insert(e1)
        )
    }
  } holds /* verified by Leon */

  /**
   * h1.merge(h2) ~ h2.merge(h1)
   */
  def heap_merge_comm_prop (h1: Heap, h2: Heap): Boolean = {
    require(h1.isHeap && h2.isHeap)
    h1.merge(h2) ~ h2.merge(h1) because {
      bisim_merge(h1, h2, h1, h2) &&
        bisim_merge(h2, h1, h2, h1) &&
        permutation_concat_comm(h1, h2) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, h2 ++ h1) &&
        // The following line is weird. It is not needed in logic,
        // but Leon cannot prove this lemma without it.
        permutation(h2 ++ h1, h2.merge(h1)) && // WEIRD!!
        permutation_tran(h1.merge(h2), h2 ++ h1, h2.merge(h1))
    }
  } holds /* verified by Leon */
}

case class HeapADT (list: List[BigInt]) {

  implicit def asHeap (l: List[BigInt]) = HeapADT(l)

  def ~ (l: List[BigInt]) = permutation(list, l)

  def findMin: Option[BigInt] = {
    if (list == Nil[BigInt]())
      None[BigInt]()
    else
      Some(min(list))
  }

  def deleteMin: List[BigInt] = {
    if (list == Nil[BigInt]())
      list
    else
      delete(list, list.findMin.get)
  }

  def merge (l: List[BigInt]): List[BigInt] = list ++ l

  def insert (e: BigInt): List[BigInt] = e :: list

  def toSortedList: List[BigInt] = sort(list)
}
