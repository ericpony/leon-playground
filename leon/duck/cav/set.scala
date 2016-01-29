import duck.collection._
import duck.proof.DeleteOps._
import duck.proof.PermutationLemmas._
import duck.proof.PermutationOps._
import duck.proof.PermutationSpec._
import leon.annotation._
import leon.lang._
import leon.proof._
import ListSetLemmas._
import ListSetOps._

import scala.language.postfixOps

object SetAggregationProof {

  def corr[V] (m1 : (V, List[V]), m2 : (V, List[V])) = m1._1 == m2._1 && m1._2 ~ m2._2

  def min (a : BigInt, b : BigInt) = if (a > b) b else a

  def comb_assoc_lemma (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt]), m3 : (BigInt, List[BigInt])) = {
    require(distinct(m1._2) && distinct(m2._2) && distinct(m3._2))
    corr(comb(m1, comb(m2, m3)), comb(comb(m1, m2), m3)) because
      union_assoc(m1._2, m2._2, m3._2)
  } holds

  def comb_comm_lemma (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt])) = {
    require(distinct(m1._2) && distinct(m2._2))
    corr(comb(m1, m2), comb(m2, m1)) because
      union_comm(m1._2, m2._2)
  } holds

  def comb (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt])) : (BigInt, List[BigInt]) = {
    (min(m1._1, m2._1), union(m1._2, m2._2))
  }

  def insert_invariant[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(distinct(l1) && distinct(l2) && l1 ~ l2)
    val L1 = insert(l1, e)
    val L2 = insert(l2, e)
    distinct(L1) && distinct(L2) && L1 ~ L2
  } holds

  def union_invariant[T] (x1 : List[T], x2 : List[T], y1 : List[T], y2 : List[T]) : Boolean = {
    require(x1 ~ y1 && x2 ~ y2)
    union(x1, x2) ~ union(y1, y2) because {
      permutation_concat(x1, x2, y1, y2) &&
        uniquate_perm(x1 ++ x2, y1 ++ y2)
    }
  } holds

  def union_comm[V] (l1 : List[V], l2 : List[V]) : Boolean = {
    union(l1, l2) ~ union(l2, l1) because {
      permutation_concat_comm(l1, l2) &&
        uniquate_perm(l1 ++ l2, l2 ++ l1)
    }
  } holds

  /* REMARK: Need ~20 seconds to verify. */
  def union_assoc[V] (l1 : List[V], l2 : List[V], l3 : List[V]) : Boolean = {
    require(distinct(l1) && distinct(l2) && distinct(l3))
    union(l1, union(l2, l3)) ~ union(union(l1, l2), l3) because {
      if (l1.isEmpty) {
        l1 ++ union(l2, l3) == union(l2, l3) &&
          union(l1, l2) ++ l3 == l2 ++ l3 because union_identity(l2) &&
          union(l1, union(l2, l3)) == union(l2, l3) because union_identity(union(l2, l3))
      } else {
        val h = l1.head
        val tl = l1.tail
        union(tl, union(l2, l3)) ~ union(union(tl, l2), l3) because {
          union_assoc(tl, l2, l3)
        } && {
          if (l2.contains(h)) {
            union(l1, union(l2, l3)) == union(tl, union(l2, l3)) because {
              uniquate_contains(l2 ++ l3, h) &&
                delete_contains_uniquate(l1 ++ union(l2, l3), h)
            } &&
              union(union(tl, l2), l3) ~ union(union(l1, l2), l3) because {
              //union(tl, l2) == union(l1, l2) because
              delete_contains_uniquate(l1 ++ l2, h) &&
                permutation_eq(union(tl, l2), union(l1, l2)) &&
                permutation_append(union(tl, l2), union(l1, l2), l3) &&
                uniquate_perm(union(tl, l2) ++ l3, union(l1, l2) ++ l3)
            }
          } else if (l3.contains(h)) {
            /// !l2.contains(h) && l3.contains(h)
            union(l1, union(l2, l3)) == union(tl, union(l2, l3)) because {
              uniquate_contains(l2 ++ l3, h) &&
                delete_contains_uniquate(l1 ++ union(l2, l3), h)
            } &&
              union(union(tl, l2), l3) ~ union(union(l1, l2), l3) because {
              delete_contains_uniquate(union(l1, l2) ++ l3, h) &&
                permutation_eq(union(union(tl, l2), l3), union(union(l1, l2), l3))
            }
          } else {
            /// !(l2 ++ l3).contains(h)
            union(l1, union(l2, l3)) == Cons(h, union(tl, union(l2, l3))) because {
              delete_uniquate_assoc(l1 ++ union(l2, l3), h)
            } &&
              union(union(l1, l2), l3) == Cons(h, union(union(tl, l2), l3))
          }
        }
      }
    }
  } holds

  @induct
  def union_identity[V] (l : List[V]) : Boolean = {
    require(distinct(l))
    union(Nil[V](), l) == l && union(l, Nil[V]()) == l because
      union_comm(l, Nil[V]())
  } holds
}

object ListSetOps {

  def insert[V] (l : List[V], e : V) : List[V] = {
    if (l.contains(e)) l
    else e :: l
  } ensuring {
    distinct(l) ==> distinct(_)
  }

  def union[T] (l1 : List[T], l2 : List[T]) : List[T] = {
    (l1 ++ l2).distinct
  } ensuring {
    distinct(_) because uniquate_is_distinct(l1 ++ l2)
  }
}

object ListSetLemmas {

  def distinct[T] (list : List[T]) : Boolean = {
    list match {
      case Nil() => true
      case Cons(hd, tl) => !tl.contains(hd) && distinct(tl)
    }
  }

  @induct
  def uniquate_contains[T] (list : List[T], e : T) : Boolean = {
    (list.contains(e) ==> list.distinct.contains(e)) &&
      (list.distinct.contains(e) ==> list.contains(e))
  } holds

  @induct
  def uniquate_not_contains[T] (list : List[T], e : T) : Boolean = {
    ((!list.contains(e)) ==> (!list.distinct.contains(e))) &&
      ((!list.distinct.contains(e)) ==> (!list.contains(e)))
  } holds

  @induct
  def uniquate_is_distinct[T] (list : List[T]) : Boolean = {
    distinct(list.distinct)
  } holds

  @induct
  def delete_neq_contains[T] (list : List[T], x : T, y : T) : Boolean = {
    require(list.contains(x) && x != y)
    delete(list, y).contains(x)
  } holds

  @induct
  def delete_neq_not_contains[T] (list : List[T], x : T, y : T) : Boolean = {
    require(!list.contains(x) && x != y)
    !delete(list, y).contains(x)
  } holds

  def delete_uniquate_assoc[T] (list : List[T], e : T) : Boolean = {
    require(!delete(list, e).contains(e))
    delete(list, e).distinct == delete(list.distinct, e) because {
      list match {
        case Nil() => trivial
        case Cons(hd, tl) =>
          if (hd == e) {
            uniquate_not_contains(tl, hd)
          } else if (tl.distinct.contains(hd)) {
            uniquate_contains(tl, hd) &&
              delete_neq_contains(tl, hd, e) &&
              uniquate_contains(delete(tl, e), hd) &&
              delete_uniquate_assoc(tl, e)
          } else {
            uniquate_not_contains(tl, hd) &&
              delete_neq_not_contains(tl, hd, e) &&
              delete_uniquate_assoc(tl, e)
          }
      }
    }
  } holds

  def delete_contains_uniquate[T] (list : List[T], e : T) : Boolean = {
    require(delete(list, e).contains(e))
    list.distinct == delete(list, e).distinct because {
      list match {
        case Nil() => trivial
        case Cons(hd, tl) =>
          if (hd == e) uniquate_contains(tl, hd)
          else delete_contains_uniquate(tl, e)
      }
    }
  } holds

  def cons_distinct_assoc[T] (list : List[T], e : T) : Boolean = {
    require(!list.contains(e))
    Cons(e, list.distinct) == Cons(e, list).distinct
  } holds

  def permutation_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && l1.contains(e))
    l2.contains(e)
  } holds //tbd

  def permutation_not_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && !l1.contains(e))
    !l2.contains(e)
  } holds //tbd

  def perm_delete_contains[T] (l1 : List[T], l2 : List[T], e : T) : Boolean = {
    require(permutation(l1, l2) && delete(l1, e).contains(e))
    delete(l2, e).contains(e) because {
      permutation_delete(l1, l2, e)
    }
  } holds //tbd

  def uniquate_cons[T] (l : List[T], e : T) : Boolean = {
    require(l.contains(e))
    l.distinct == Cons(e, l).distinct because {
      delete_contains_uniquate(Cons(e, l), e)
    }
  } holds

  def uniquate_perm[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l1.distinct, l2.distinct) because {
      l1 match {
        case Nil() => trivial
        case Cons(hd, tl) =>
          if (tl.contains(hd)) {
            permutation_delete(l1, l2, hd) &&
              uniquate_perm(tl, delete(l2, hd)) &&
              delete_contains_uniquate(l2, hd) &&
              permutation_refl(l2.distinct) &&
              uniquate_cons(tl, hd) &&
              permutation_tran(tl.distinct, delete(l2, hd).distinct, l2.distinct)
          } else {
            // !tl.contains(hd) &&
            cons_distinct_assoc(tl, hd) &&
              permutation_delete(l1, l2, hd) &&
              uniquate_perm(tl, delete(l2, hd)) &&
              delete_uniquate_assoc(l2, hd) &&
              uniquate_contains(l2, hd) &&
              permutation_cons_delete(l2.distinct, hd)
          }
      }
    }
  } holds
}
