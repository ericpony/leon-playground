package duck.proof

import duck.proof.sugar._
import duck.proof.DistinctSpec._
import duck.proof.DistinctOps._
import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.DeleteOps._
import duck.proof.DeleteSpec._
import duck.collection.DistinctListSetOps._
import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

/**
 * TODO: prove
 * union_insert_delete_permutation,  union_permutation_3, union_permutation_4.
 */
object DistinctListSetLemmas {
  @induct
  def insert_distinct[V] (set: List[V], e: V): Boolean = {
    require(distinct(set))
    distinct(insert(set, e))
  } holds /* verified */

  @induct
  def insert_contains[V] (set: List[V], e: V): Boolean = {
    require(set contains e)
    insert(set, e) == set
  } holds /* verified */

  @induct
  def insert_not_contains[V] (set: List[V], e: V): Boolean = {
    require(!set.contains(e))
    insert(set, e) == set ++ Cons(e, Nil[V])
  } holds /* verified */

  @induct
  def insert_comm_permutation[V] (set: List[V], e: V, f: V): Boolean = {
    if (set contains e) {
      insert_contains(set, e) &&
        insert_contains(insert(set, f), e) &&
        permutation_refl(insert(set, f)) &&
        permutation(insert(insert(set, e), f), insert(insert(set, f), e))
    } else if (set contains f) {
      insert_contains(set, f) &&
        insert_contains(insert(set, e), f) &&
        permutation_refl(insert(set, e)) &&
        permutation(insert(insert(set, e), f), insert(insert(set, f), e))
    } else {
      permutation(insert(insert(set, e), f), insert(insert(set, f), e))
    }
  } holds /* verified */

  def insert_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(permutation(s, t))
    if (s contains e) {
      t.contains(e) &&
        insert_contains(s, e) &&
        insert_contains(t, e) &&
        permutation(insert(s, e), insert(t, e))
    } else {
      !t.contains(e) &&
        insert_not_contains(s, e) &&
        insert_not_contains(t, e) &&
        permutation_concat(s, t, Cons(e, Nil[V])) &&
        permutation(insert(s, e), insert(t, e))
    }
  } holds /* verified */

  @induct
  def remove_distinct[V] (set: List[V], e: V): Boolean = {
    require(distinct(set))
    distinct(remove(set, e))
  } holds /* verified */

  @induct
  def remove_contains[V] (set: List[V], e: V): Boolean = {
    require(set contains e)
    remove(set, e) == delete(set, e)
  } holds /* verified */

  @induct
  def remove_not_contains[V] (set: List[V], e: V): Boolean = {
    require(!set.contains(e))
    remove(set, e) == set
  } holds /* verified */

  def remove_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(permutation(s, t))
    if (s contains e) {
      t.contains(e) &&
        remove_contains(s, e) &&
        remove_contains(t, e) &&
        permutation_delete(s, t, e) &&
        permutation(remove(s, e), remove(t, e))
    } else {
      !t.contains(e) &&
        remove_not_contains(s, e) &&
        remove_not_contains(t, e) &&
        permutation(remove(s, e), remove(t, e))
    }
  } holds /* verified */

  //  /* This property now follows from the post-condition of union */
  //  @induct
  //  def union_content[V] (s: List[V], t: List[V]): Boolean = {
  //    if (s.isEmpty) {
  //      union(s, t).content == s.content ++ t.content
  //    } else {
  //      union(s, t).content == s.content ++ t.content
  //    }
  //  } holds

  @induct
  def union_distinct[V] (s: List[V], t: List[V]): Boolean = {
    require(distinct(s) && distinct(t))
    distinct(union(s, t)) because {
      if (s.isEmpty) trivial
      else {
        union_distinct(s.tail, t) &&
          insert_distinct(union(s.tail, t), s.head)
      }
    }
  } holds /* verified */

  @induct
  def union_insert_delete_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(s contains e)
    if (s.head == e) {
      permutation_refl(union(s, t)) &&
        permutation(insert(union(delete(s, e), t), e), union(s, t))
    } else {
      check { union_insert_delete_permutation(s.tail, t, e) } &&
        check {
          permutation(insert(union(delete(s.tail, e), t), e),
            union(s.tail, t))
        } &&
        check {
          insert_permutation(insert(union(delete(s.tail, e), t), e), union(s.tail, t),
            s.head)
        } &&
        insert_comm_permutation(union(delete(s.tail, e), t), s.head, e) &&
        check {
          permutation_tran(insert(insert(union(delete(s.tail, e), t), s.head), e),
            insert(insert(union(delete(s.tail, e), t), e), s.head),
            insert(union(s.tail, t), s.head))
        } &&
        check {
          union(delete(s, e), t) ==
            insert(union(delete(s.tail, e), t), s.head)
        } &&
        check { delete(s, e).head == s.head } &&
        check { delete(s, e).tail == delete(s.tail, e) } &&
        check { permutation(insert(union(delete(s, e), t), e), union(s, t)) }
    }
  } holds /* timeout */

  def union_permutation[V] (s: List[V], t: List[V], u: List[V], v: List[V]): Boolean = {
    require(permutation(s, u) && permutation(t, v))
    permutation(union(s, t), union(u, v)) because {
      if (s.isEmpty) trivial
      else {
        union_permutation(s.tail, t, delete(u, s.head), v) &&
          insert_permutation(
            union(s.tail, t),
            union(delete(u, s.head), v),
            s.head) &&
          union_permutation_2(s, t, u, v) &&
          union_permutation_3(s, t, u, v) &&
          union_permutation_4(s, t, u, v) &&
          permutation_tran(
            insert(union(s.tail, t), s.head),
            insert(union(delete(u, s.head), v), s.head),
            union(u, v))
      }
    }
  } holds /* verified */

  @induct
  def union_permutation_2[V] (s: List[V], t: List[V], u: List[V], v: List[V]): Boolean = {
    require(permutation(s, u) && permutation(t, v) && s != Nil[V]())
    insert(union(s.tail, t), s.head) == union(s, t) because
      union_insert_delete_permutation(s, t, s.head)
  } holds /* verified */

  @induct
  def union_permutation_3[V] (s: List[V], t: List[V], u: List[V], v: List[V]): Boolean = {
    require(permutation(s, u) && permutation(t, v) && s != Nil[V]())
    permutation(
      insert(union(s.tail, t), s.head),
      insert(union(delete(u, s.head), v), s.head)
    )
  } holds /* timeout */

  @induct
  def union_permutation_4[V] (s: List[V], t: List[V], u: List[V], v: List[V]): Boolean = {
    require(permutation(s, u) && permutation(t, v) && s != Nil[V]())
    permutation(insert(union(delete(u, s.head), v), s.head), union(u, v)) because
      union_insert_delete_permutation(s, t, s.head)
  } holds /* timeout */
}
