import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import MinOps._
import MinSpec._
import DeleteOps._
import DeleteSpec._
import PermutationOps._
import PermutationSpec._
import SortedListOps._
import SortedListLemmas._
import scala.language.postfixOps

object SortedListSpec {
  /* Insert operations are commutative. */
  @induct
  def insert_commutative_prop (list: List[BigInt], e1: BigInt, e2: BigInt) = {
    require(isSorted(list))
    insert(insert(list, e1), e2) == insert(insert(list, e2), e1)
  } holds /* verified by Leon */

  /* Merge operations are associative. */
  def sort_associative_prop (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) = {
    sort (sort (l1 ++ l2) ++ l3) == sort (l1 ++ sort (l2 ++ l3)) because
      // permutation (l1 ++ l2, sort (l1 ++ l2))
      sort_permutation (l1 ++ l2) &&
      // permutation (sort (l1 ++ l2), l1 ++ l2)
      permutation_comm (l1 ++ l2, sort (l1 ++ l2)) &&
      // permutation (sort (l1 ++ l2) ++ l3, l1 ++ l2 ++ l3)
      permutation_concat (sort (l1 ++ l2), l1 ++ l2, l3) &&
      // permutation (l2 ++ l3, sort (l2 ++ l3))
      sort_permutation (l2 ++ l3) &&
      // permutation (l1 ++ (l2 ++ l3), l1 ++ sort (l2 ++ l3)
      concat_permutation (l1, l2 ++ l3, sort (l2 ++ l3)) &&
      // permutation (l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3))
      permutation_concat_assoc (l1, l2, l3) &&
      permutation_tran (sort (l1 ++ l2) ++ l3, l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) &&
      permutation_tran (sort (l1 ++ l2) ++ l3, l1 ++ (l2 ++ l3), l1 ++ sort (l2 ++ l3)) &&
      permutation_sort (sort (l1 ++ l2) ++ l3, l1 ++ sort (l2 ++ l3))
  } holds

  /* Merge operations are commutative. */
  def sort_commutative_prop (l1: List[BigInt], l2: List[BigInt]) = {
    sort (l1 ++ l2) == sort (l2 ++ l1) because
      permutation_concat_comm (l1, l2) &&
      permutation_sort (l1 ++ l2, l2 ++ l1)
  } holds /* verified by Leon */

  /* Sort operations are idempotent. */
  def sort_idempotent_prop (list: List[BigInt]) = {
    sort(list) == sort(sort(list)) because 
    check {
      sort_permutation (list) &&
      permutation_sort (list, sort (list))
    }
  } holds /* verified by Leon */

  /* Sort any permutation of a list give the same result */
  def sort_permutation_prop (l1: List[BigInt], l2: List[BigInt]) = {
    require(permutation (l1, l2))
    sort(l1) == sort(l2) because permutation_sort (l1, l2)
  } holds

  /* Sort is permutation */
  def permutation_sort_prop (list : List[BigInt]) = {
    permutation (list, sort (list)) because sort_permutation (list)
  } holds
}

object SortedListOps {
  /**
   * Insert an element into a sorted list.
   * @param list a sorted list
   * @param e an element
   * @return a sorted list containning e
   */
  def insert (list: List[BigInt], e: BigInt): List[BigInt] = {
    require(isSorted(list))
    list match {
      case Nil()       => Cons(e, Nil())
      case Cons(x, xs) => if (x >= e) Cons(e, list) else Cons(x, insert(xs, e))
    }
  } ensuring (res => res.content == list.content ++ Set[BigInt](e) &&
    res.size == list.size + 1 &&
    isSorted(res)) /* verified by Leon */

  /**
   * Merge two sorted lists to obtain one sorted list.
   * @param l1 a sorted list
   * @param l2 a sorted list
   * @return a sorted list
   */
  @induct
  def mergeSortedList (l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    l2 match {
      case Nil()       => l1
      case Cons(x, xs) => insert(mergeSortedList(l1, xs), x)
    }
  } ensuring {
    res => isSorted(res) && res.content == l1.content ++ l2.content
  } /* verified by Leon */

  /**
   * Obtain a sorted version of the provided list (in ascending order).
   * @param list a list
   * @return a sorted list
   */
  def sort (list: List[BigInt]): List[BigInt] = {
    list match {
      case Nil()       => list
      case Cons(x, xs) => insert(sort(xs), x)
    }
  } ensuring {
    res => res.content == list.content && isSorted(res)
  } /* verified by Leon */

  /**
   * Tell whether a list is sorted in ascending order.
   * @param list a list
   * @return whether the input list is sorted in ascending order
   */
  def isSorted (list: List[BigInt]): Boolean = {
    list match {
      case Nil()                  => trivial
      case Cons(_, Nil())         => trivial
      case Cons(x1, Cons(x2, xs)) => x1 <= x2 && isSorted(list.tail)
    }
  } ensuring {
    res => list.size == 0 || !res || list.head == min(list)
  }
}

object SortedListLemmas {
  /**
   * Check that the sort(list).head == min(list).
   */
  @induct
  def min_head_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    sort(list).head == min(list)
  } holds /* verified by Leon */

  @induct
  def min_sort_lemma (list: List[BigInt]) = {
    require(list != Nil[BigInt]())
    min(sort(list)) == min(list)
  } holds

  @induct
  def sort_delete_lemma (list: List[BigInt], m: BigInt): Boolean = {
    require(list != Nil[BigInt]() && m == sort(list).head)
    sort(delete(list, m)) == delete(sort(list), m)
  } holds /* verified by leon */

  @induct
  def sort_not_contains_lemma (list : List[BigInt], e : BigInt) : Boolean = {
    require (!list.contains (e))
    !sort (list).contains (e)
  } holds

  @induct
  def insert_comm (list : List[BigInt], a : BigInt, b : BigInt) : Boolean = {
    require (isSorted (list))
    insert (insert (list, a), b) == insert (insert (list, b), a)
  } holds

  @induct
  def insert_delete (list : List[BigInt], e : BigInt) : Boolean = {
    require (isSorted (list))
    list == delete (insert (list, e), e)
  } holds

  def sort_cons_delete (list : List[BigInt], e : BigInt) : Boolean = {
    sort (list) == delete (sort (Cons (e, list)), e) because
      check { insert_delete (sort (list), e) }
  } holds

  @ignore
  @induct
  def permutation_cons_sort (list : List[BigInt], e : BigInt) : Boolean = {
    if (list.size == 0) {
      permutation (Cons (e, sort (list)), sort (Cons (e, list)))
    } else {
      delete (sort (Cons (e, list)), e) == sort (list) because
        sort_delete_lemma (Cons (e, list), e) &&
        delete (Cons (e, list), e) == list
/*
      permutation (Cons (e, sort (list)), sort (Cons (e, list))) because
        (sort (Cons (e, list)) contains e) && 
        delete (sort (Cons (e, list)), e) == sort (list) &&
        permutation_refl (sort (list))
 */
    }
  } holds
  
  @induct
  def insert_sort_delete (list : List[BigInt], e : BigInt) : Boolean = {
    require (list.contains (e))
    if (list.size == 1) {
      sort (list) == insert (sort (delete (list, e)), e)
    } else {
      val h = list.head
      if (h == e) {
        sort (list) == insert (sort (delete (list, e)), e)
      } else {
        sort (list) == insert (sort (delete (list, e)), e) because
          check { 
            insert_sort_delete (list.tail, e) &&
            insert_comm (sort (delete (list.tail, e)), e, h)
          }
      }
    }
  } holds

  @induct
  def permutation_sort (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    if (l1 == Nil[BigInt]()) {
      sort (l1) == sort (l2)
    } else {
      val h1 = l1.head
      sort (l1) == sort (l2) because 
        check { permutation_sort (l1.tail, delete (l2, h1)) } &&
        check { insert_sort_delete (l2, h1) }
    }
  } holds

  @induct
  def sort_permutation (list : List[BigInt]) : Boolean = {
    if (list == Nil[BigInt]) {
      permutation (list, sort (list))
    } else {
      val h = list.head
      permutation (list, sort (list)) because
        check { sort_permutation (list.tail) &&
                sort_cons_delete (list.tail, list.head) }
    }
  } holds
}
