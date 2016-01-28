package duck.spec

import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.DeleteOps._
import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._
import scala.language.postfixOps

object DistinctListUnion {

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

  def cons_distinct_assoc[T] (list : List[T], e : T) : Boolean = {
    require(!list.contains(e))
    Cons(e, list.distinct) == Cons(e, list).distinct
  } holds

  def cons_delete_uniquate_perm[T] (list : List[T], e : T) : Boolean = {
    require(list.contains(e))
    permutation(Cons(e, delete(list, e)).distinct, list.distinct) because {
      list match {
        case Nil() => trivial
        case Cons(hd, tl) =>
          if (hd == e) permutation_refl(list.distinct)
          else {
            check{tl.contains(e)} //
          }
      }
    }
  } holds // unknown

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

  def union[T] (l1 : List[T], l2 : List[T]) : List[T] = {
    (l1 ++ l2).distinct
  }

  def uniquate_perm[T] (l1 : List[T], l2 : List[T]) : Boolean = {
    require(permutation(l1, l2))
    permutation(l1.distinct, l2.distinct) because {
      l1 match {
        case Nil() => check{permutation(l1.distinct, l2.distinct)}
        case Cons(hd, tl) =>
          if (tl.distinct.contains(hd)) {
            permutation_delete(l1, l2, hd) && uniquate_perm(tl, delete(l2, hd)) && delete_contains_uniquate(l2, hd) &&
            check{permutation(l1.distinct, l2.distinct)}
          } else {
            permutation_delete(l1, l2, hd) && uniquate_perm(tl, delete(l2, hd)) &&
            uniquate_not_contains(tl, hd) && check{!delete(l2, hd).contains(hd)} &&
            cons_distinct_assoc(delete(l2, hd), hd) && check{Cons(hd, delete(l2, hd).distinct) == Cons(hd, delete(l2, hd)).distinct} &&
            check{l2.contains(hd)}
          }
      }
    }
  } holds // unknown

/*
  def union_perm[T] (x1 : List[T], x2 : List[T], y1 : List[T], y2 : List[T]) : Boolean = {
    require(permutation(x1, y1) && permutation(x2, y2))
    permutation(union(x1, x2), union(y1, y2))
  } holds //
*/
}
