package duck.spec

import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.DeleteOps._
import duck.proof.sugar._
import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._
import DistinctListOps._
import scala.language.postfixOps

case class DistinctList[V] (list : List[V]) {

  def insert (e : V) : List[V] = {
    require(distinct(list))
    DistinctListOps.insert(list, e)
  } ensuring {distinct(_)}

  def insertAll (other : List[V]) = {
    require(distinct(list) && distinct(other))
    union(list, other)
  } ensuring {distinct(_)}

  def remove (e : V) : List[V] = {
    require(distinct(list))
    DistinctListOps.remove(list, e)
  } ensuring {distinct(_)}
}

object DistinctListOps {

  /**
    * Tell whether a list contains no duplicate elements.
    * @param list a list
    * @return whether list contains no duplicate elements
    */
  def distinct[V] (list : List[V]) : Boolean = {
    if (list == Nil[V]()) trivial
    else !list.tail.contains(list.head) && distinct(list.tail)
  }

  def insert[V] (set : List[V], e : V) : List[V] = {
    //    if (set.isEmpty) Cons(e, Nil[V])
    //    else if (set.head == e) set
    //    else set.head :: insert(set.tail, e)
    if (set.contains(e))
      set
    else
      e :: set
  } ensuring {
    res => res.content == set.content ++ Set(e) &&
      (if (set.contains(e))
        res.size == set.size
      else
        res.size == set.size + 1) &&
      (distinct(set) implies distinct(res))
  }

  @induct // we need this form of remove to do reduction
  def remove[V] (list : List[V], e : V) : List[V] = {
    delete(list, e)
  } ensuring {
    distinct(list) implies distinct(_)
  }

  @induct
  def union[V] (s : List[V], t : List[V]) : List[V] = {
    //require(distinct(s) && distinct(t))
    //    s match {
    //      case Nil() => t
    //      case Cons(sh, st) => union(st, insert(t, sh))
    //    }
    if (s == Nil[V]()) t
    else if (t == Nil[V]()) s
    // The relative order of distinct elements is kept
    else s.foldRight(t)((e, tt) => insert(tt, e))
  } ensuring {
    res =>
      res.content == s.content ++ t.content &&
        // res.size == s.size + t.size - (s & t).size &&
        res.size <= s.size + t.size &&
        ((distinct(s) && distinct(t)) implies distinct(res))
  }
}

object DistinctListLemmas {

  @induct
  def insert_comm_permutation[V] (set : List[V], e : V, f : V) : Boolean = {
    //require(distinct(set))
    permutation(insert(insert(set, e), f), insert(insert(set, f), e))
  } holds /* verified */

  def insert_permutation[V] (s : List[V], t : List[V], e : V) : Boolean = {
    require(permutation(s, t)) // && distinct(s) && distinct(t))
    permutation(insert(s, e), insert(t, e))
  } holds /* verified */

  def delete_permutation[V] (s : List[V], t : List[V], e : V) : Boolean = {
    require(permutation(s, t)) // && distinct(s) && distinct(t))
    permutation(delete(s, e), delete(t, e)) because {
      if (!s.contains(e))
        trivial
      else
        permutation_delete(s, t, e)
    }
  } holds /* verified */

  @induct
  def delete_distinct[V] (set : List[V], e : V) : Boolean = {
    require(distinct(set))
    distinct(delete(set, e))
  } holds /* verified */

  //  def union_comm (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
  //    require(distinct(l1) && distinct(l2))
  //    val L1 = union(l1, l2)
  //    val L2 = union(l2, l1)
  //    permutation(L1, L2) because {
  //      if (l1 == Nil[BigInt]() || l2 == Nil[BigInt]())
  //        permutation_refl(L1)
  //      else {
  //        check {!delete(l2, l1.head).contains(l1.head)} &&
  //          union_comm(l1, delete(l2, l1.head)) &&
  //          check {union(l1, delete(l2, l1.head)) == L1} &&
  //          permutation_comm(delete(L2, L1.head), L1.tail) &&
  //          permutation_delete_cons(L2, L1.head, L1.tail) &&
  //          permutation_comm(L2, L1)
  //      }
  //    }
  //  } holds

  //  def union_insert_delete_permutation[V] (s : List[V], t : List[V], e : V) : Boolean = {
  //    require(s.contains(e))// && distinct(s) && distinct(t))
  //    permutation(
  //      insert(union(delete(s, e), t), e),
  //      union(s, t)
  //    ) because {
  //      if (s.head == e) {
  //        union_insert_delete_permutation_2(s, t)
  //      } else {
  //        union_insert_delete_permutation_3(s, t, e) &&
  //          insert_permutation(
  //            insert(union(delete(s.tail, e), t), e),
  //            union(s.tail, t), s.head) &&
  //          insert_comm_permutation(
  //            union(delete(s.tail, e), t),
  //            s.head, e) &&
  //          permutation_tran(
  //            insert(insert(union(delete(s.tail, e), t), s.head), e),
  //            insert(insert(union(delete(s.tail, e), t), e), s.head),
  //            insert(union(s.tail, t), s.head))
  //      }
  //    }
  //  } holds /* verified */
  //
  //  def union_insert_delete_permutation_2[V] (s : List[V], t : List[V]) : Boolean = {
  //    require(s != Nil[V]())// && distinct(s) && distinct(t))
  //    permutation(
  //      insert(union(s.tail, t), s.head),
  //      union(s, t)
  //    ) because {
  //      insert(union(s.tail, t), s.head) == union(s, t) &&
  //        permutation_eq(insert(union(s.tail, t), s.head), union(s, t))
  //    }
  //  } holds /* verified */
  //
  //  def union_insert_delete_permutation_3[V] (s : List[V], t : List[V], e : V) : Boolean = {
  //    require(s != Nil[V]() && s.tail.contains(e))// && distinct(s) && distinct(t))
  //    permutation(
  //      insert(union(delete(s.tail, e), t), e),
  //      union(s.tail, t)
  //    ) because
  //      union_insert_delete_permutation(s.tail, t, e)
  //  } holds /* verified */
  //
  //  def union_permutation[V] (s : List[V], t : List[V], u : List[V], v : List[V]) : Boolean = {
  //    require(permutation(s, u) && permutation(t, v))// && distinct(s) && distinct(t) && distinct(u) && distinct(v))
  //    permutation(union(s, t), union(u, v)) because {
  //      if (s.isEmpty) trivial
  //      else {
  //        union_permutation(s.tail, t, delete(u, s.head), v) &&
  //          insert_permutation(
  //            union(s.tail, t),
  //            union(delete(u, s.head), v),
  //            s.head) &&
  //          union_permutation_2(s, t, u, v) &&
  //          union_permutation_3(s, t, u, v) &&
  //          permutation_tran(
  //            insert(union(s.tail, t), s.head),
  //            insert(union(delete(u, s.head), v), s.head),
  //            union(u, v))
  //      }
  //    }
  //  } holds /* verified */
  //
  //  def union_permutation_2[V] (s : List[V], t : List[V], u : List[V], v : List[V]) : Boolean = {
  //    require(permutation(s, u) && permutation(t, v) && s != Nil[V]())// && distinct(s) && distinct(t) && distinct(u) && distinct(v))
  //    permutation(
  //      insert(union(s.tail, t), s.head),
  //      insert(union(delete(u, s.head), v), s.head)
  //    ) because {
  //      union_permutation(s.tail, t, delete(u, s.head), v) &&
  //        permutation(union(s.tail, t), union(delete(u, s.head), v)) &&
  //        insert_permutation(union(s.tail, t), union(delete(u, s.head), v), s.head)
  //    }
  //  } holds /* verified */
  //
  //  def union_permutation_3[V] (s : List[V], t : List[V], u : List[V], v : List[V]) : Boolean = {
  //    require(permutation(s, u) && permutation(t, v) && s != Nil[V]())// && distinct(s) && distinct(t) && distinct(u) && distinct(v))
  //    permutation(
  //      insert(union(delete(u, s.head), v), s.head),
  //      union(u, v)
  //    ) because
  //      union_insert_delete_permutation(u, v, s.head)
  //  } holds /* verified */
}
