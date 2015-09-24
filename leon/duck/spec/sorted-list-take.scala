package duck.proof

import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.MinSpec._
import duck.proof.MinOps._
import duck.proof.MinLemmas._
import duck.spec.SortedListOps._
import duck.spec.SortedListSpec._
import duck.spec.SortedListLemmas._
import duck.spec.ListSpecs._
import duck.collection.List._
import leon.annotation._
import leon.lang._
import leon.proof._
import DeleteSpec._
import DeleteOps._
import DeleteLemmas._
import SortedListTakeOps._
import SortedListTakeLemmas._

import scala.language.postfixOps

object SortedListTakeSpec {
  def combOp_comm (l1: List[BigInt], l2: List[BigInt], n: BigInt) = {
    combOp(l1, l2, n) == combOp(l2, l1, n) because
      combOp_comm_lemma(l1, l2, n)
  } holds
}

object SortedListTakeOps {
  def sorted_take (list: List[BigInt], i: BigInt): List[BigInt] = {
    require(isSorted(list))
    (list, i) match {
      case (Nil(), _)      => Nil[BigInt]()
      case (Cons(h, t), i) =>
        if (i <= BigInt(0)) {
          Nil[BigInt]()
        } else {
          Cons(h, sorted_take(t, i - 1))
        }
    }
  } ensuring {
    res => res == list.take(i) && isSorted(res)
  }

  def sort_take (list: List[BigInt], n: BigInt): List[BigInt] = {
    sorted_take(sort(list), n)
  } ensuring {
    res => res.content.subsetOf(list.content) && isSorted(res) && res.size == (
      if (n <= 0) BigInt(0)
      else if (n > list.size) list.size
      else n
      )
  }

  def seqOp (list: List[BigInt], e: BigInt, n: BigInt) = {
    sort_take(e :: list, n)
  }

  def combOp (l1: List[BigInt], l2: List[BigInt], n: BigInt) = {
    sort_take(l1 ++ l2, n)
  }
}

object SortedListTakeLemmas {

  def take_all (l : List[BigInt], n : BigInt) : Boolean = {
    require(n >= l.size)
    l.take(n) == l because {
      l match {
        case Nil() => trivial
        case Cons(h, t) =>
          if (n <= BigInt(0)) {
            trivial
          } else {
            take_all(t, n - 1)
          }
      }
    }
  } holds

  def take_n_m (l : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    l.take(n).take(m) == l.take(min(n, m)) because {
      l match {
        case Nil() => trivial
        case Cons(h, t) =>
          if (n <= 0 || m <= 0)
            trivial
          else if (n < m) {
            take_all(l.take(n), m)
          } else {
            take_n_m(t, n - 1, m - 1)
          }
      }
    }
  } holds

  def take_idempotent (l : List[BigInt], n : BigInt) : Boolean = {
    l.take(n).take(n) == l.take(n) because { take_n_m(l, n, n) }
  } holds

  def sort_take_idempotent (l : List[BigInt], n : BigInt) : Boolean = {
    sort_take(sort_take(l, n), n) == sort_take(l, n) because {
      sort_sorted(sorted_take(sort(l), n)) && take_idempotent(sort(l), n)
    }
  } holds

  def sort_tail (l : List[BigInt]) : Boolean = {
    require(!l.isEmpty)
    sort(l).tail == sort(delete(l, min(l))) because {
      min_head_lemma(l) && sort_delete_lemma(l, min(l))
    }
  } holds

  def sort_take_decomp (l : List[BigInt], n : BigInt) : Boolean = {
    require(!l.isEmpty && n > 0)
    sort(l).take(n) == min(l)::sort(delete(l, min(l))).take(n - 1) because {
      sort_tail(l)
    }
  } holds

  def sort_take_sorted (l : List[BigInt], n : BigInt) : Boolean = {
    isSorted(sort(l).take(n)) because { sort(l).take(n) == sort_take(l, n) }
  } holds

  def take_delete (l : List[BigInt], n : BigInt, x : BigInt) : Boolean = {
    require(l.take(n).contains(x))
    delete(l.take(n), x) == delete(l, x).take(n - 1) because {
      l match {
        case Nil() => trivial
        case Cons(h, t) if h == x => trivial
        case Cons(h, t) => t.take(n - 1).contains(x) && take_delete(t, n - 1, x)
      }
    }
  } holds

  def sort_take_min (l : List[BigInt], n : BigInt) : Boolean = {
    require(!l.isEmpty && n > 0)
    min(sort(l).take(n)) == min(l) because {
      l match {
        case Nil() => trivial
        case Cons(h, Nil()) => trivial
        case Cons(h, t) if n == 1 => sort_take_decomp(l, n)
        case Cons(h, t) =>
          // min(sort(l).take(n))
          // == min(min(l)::sort(delete(l, min(l))).take(n - 1))
          sort_take_decomp(l, n) &&
          // == min(min(l), min(delete(l, min(l))))
          sort_take_min(delete(l, min(l)), n - 1) &&
          // == min(l)
          min_delete(l)
      }
    }
  } holds

  def sort_take_concat_decomp_l (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require (!l1.isEmpty && n >= m && m > 0 && (l2.isEmpty || min(l1) <= min(l2)))
    sort(sort(l1).take(n) ++ l2).take(m) == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ l2).take(m - 1) because {
      val min12 = min(sort(l1).take(n) ++ l2)
      // sort_take(sort(l1).take(n) ++ l2, m)
      sort_take_decomp(sort(l1).take(n) ++ l2, m) &&
      // == min12::sort(delete(sort(l1).take(n) ++ l2, min12)).take(m - 1)
      (if (l2.isEmpty)
        rightUnitAppend(sort(l1).take(n)) && sort_take_min(l1, n)
      else
        min_concat_lemma2(sort(l1).take(n), l2) && sort_take_min(l1, n)) &&
      // == min(l1)::sort(delete(sort(l1).take(n) ++ l2, min(l1))).take(m - 1)
      min_lemma2(sort(l1).take(n)) && delete_concat(sort(l1).take(n), l2, min(sort(l1).take(n))) &&
      // == min(l1)::sort(delete(sort(l1).take(n), min(l1)) ++ l2).take(m - 1)
      take_delete(sort(l1), n, min(l1))
      // == min(l1)::sort(delete(sort(l1), min(l1)).take(n - 1) ++ l2).take(m - 1)
    }
  } holds

  def sort_take_concat_decomp_r (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require (!l2.isEmpty && m > 0 && (l1.isEmpty || n <= 0 || min(l2) < min(l1)))
    sort(sort(l1).take(n) ++ l2).take(m) == min(l2)::sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1) because {
      val min12 = min(sort(l1).take(n) ++ l2)
      // sort_take(sort(l1).take(n) ++ l2, m)
      sort_take_decomp(sort(l1).take(n) ++ l2, m) &&
      // == min12::sort(delete(sort(l1).take(n) ++ l2, min12)).take(m - 1)
      (if (l1.isEmpty || n <= 0) leftUnitAppend(l2) else min_concat_lemma2(sort(l1).take(n), l2) && sort_take_min(l1, n)) &&
      // == min(l2)::sort(delete(sort(l1).take(n) ++ l2, min(l2))).take(m - 1)
      (
        if (l1.isEmpty || n <= 0)
          leftUnitAppend(l2) && leftUnitAppend(delete(l2, min(l2)))
        else
          min_not_contains(sort(l1).take(n), min(l2)) && delete_concat_lemma1(sort(l1).take(n), l2, min(l2))
      )
      // == min(l2)::sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1)
    }
  } holds

  def sort_take_concat_more (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(n >= r && m >= r && i >= 0 && j >= 0)
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r) because {
      sort_take_concat_sort_take(l1, l2, n, m, r) && sort_take_concat_sort_take(l1, l2, n + i, m + j, r)
    }
  } holds

  def sort_take_concat_norm (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require(n >= r && m >= r)
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == sort(sort(l1).take(r) ++ sort(l2).take(r)).take(r) because {
      sort_take_concat_more (l1, l2, r, r, r, n - r, m - r)
    }
  } holds

  def sort_take_perm_eq (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) : Boolean = {
    require(permutation(l1, l2))
    sort_take(l1, n) == sort_take(l2, n) because { sort_permutation_prop(l1, l2) }
  } holds

  def sort_take_concat (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require(n >= m)
    sort_take(sort_take(l1, n) ++ l2, m) == sort_take(l1 ++ l2, m) because {
      if (n <= 0 || m <= 0 || l1.isEmpty) {
        trivial
      } else if (l2.isEmpty) {
        rightUnitAppend(sort_take(l1, n)) && sort_sorted(sort_take(l1, n)) && take_n_m(sort(l1), n, m) &&
        rightUnitAppend(l1)
      } else if (min(l1) <= min(l2)) {
        // sort_take(sort_take(l1, n) ++ l2, m)
        sort_take_concat_decomp_l(l1, l2, n, m) &&
        // == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ l2).take(m - 1)
        sort_take_concat(delete(l1, min(l1)), l2, n - 1, m -1) &&
        // == min(l1)::sort(delete(l1, min(l1)) ++ l2).take(m - 1)
        delete_concat (l1, l2, min(l1)) && min_lemma2(l1) &&
        // == min(l1)::sort(delete(l1 ++ l2, min(l1))).take(m - 1)
        min_concat_lemma2(l1, l2) && sort_take_decomp(l1 ++ l2, m)
        // == sort_take(l1 ++ l2, n)
      } else {
        // sort_take(sort_take(l1, n) ++ l2, m)
        sort_take_concat_decomp_r(l1, l2, n, m) &&
        // == min(l2)::sort(sort(l1).take(n) ++ delete(l2, min(l2))).take(m - 1)
        sort_take_concat(l1, delete(l2, min(l2)), n, m - 1) &&
        // == min(l2)::sort(l1 ++ delete(l2, min(l2))).take(m - 1)
        min_not_contains(l1, min(l2)) && !l1.contains(min(l2)) && delete_concat_lemma1(l1, l2, min(l2)) &&
        // == min(l2)::sort(delete(l1 ++ l2, min(l2))).take(m - 1)
        min_concat_lemma2(l1, l2) && min(l1 ++ l2) == min(l2) && sort_take_decomp(l1 ++ l2, m)
        // == sort_take(l1 ++ l2, m)
      }
    }
  } holds

  def sort_take_concat_sort_take (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require(n >= r && m >= r)
    sort_take(sort_take(l1, n) ++ sort_take(l2, m), r) == sort_take(l1 ++ l2, r) because {
      // sort_take(sort_take(l1, n) ++ sort_take(l2, m), r)
      sort_take_concat (l1, sort_take(l2, m), n, r) &&
      // == sort_take(l1 ++ sort_take(l2, m), r)
      combOp_comm_lemma(l1, sort_take(l2, m), r) &&
      // == sort_take(sort_take(l2, m) ++ l1, r)
      sort_take_concat (l2, l1, m, r) &&
      // == sort_take(l2 ++ l1, r)
      combOp_comm_lemma(l2, l1, r)
      // == sort_take(l1 ++ l2, r)
    }
  } holds

  def combOp_comm_lemma (l1: List[BigInt], l2: List[BigInt], n: BigInt) = {
    combOp(l1, l2, n) == combOp(l2, l1, n) because {
      sort_commutative_prop(l1, l2)
    }
  } holds

  def combOp_assoc_lemma (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt], n: BigInt) = {
    combOp(combOp(l1, l2, n), l3, n) == combOp(l1, combOp(l2, l3, n), n) because {
      // sort_take(sort_take(l1 ++ l2, n) ++ l3, n)
      sort_take_concat_sort_take(sort_take(l1 ++ l2, n), l3, n, n, n) &&
      // == sort_take(sort_take(sort_take(l1 ++ l2, n), n) ++ sort_take(l3, n), n)
      sort_take_idempotent(l1 ++ l2, n) &&
      // == sort_take(sort_take(l1 ++ l2, n) ++ sort_take(l3, n), n)
      sort_take_concat_sort_take(l1 ++ l2, l3, n, n, n) &&
      // == sort_take((l1 ++ l2) ++ l3, n)
      // sort_take(l1 ++ sort_take(l2 ++ l3, n), n)
      sort_take_concat_sort_take(l1, sort_take(l2 ++ l3, n), n, n, n) &&
      // == sort_take(sort_take(l1, n) ++ sort_take(sort_take(l2 ++ l3, n), n), n)
      sort_take_idempotent(l2 ++ l3, n) &&
      // == sort_take(sort_take(l1, n) ++ sort_take(l2 ++ l3, n), n)
      sort_take_concat_sort_take(l1, l2 ++ l3, n, n, n) &&
      // == sort_take(l1 ++ (l2 ++ l3), n)
      appendAssoc(l1, l2, l3)
      // == sort_take(l1 ++ l2 ++ l3, n)
    }
  } holds

}
