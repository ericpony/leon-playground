package duck.proof

import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.collection.SortedListOps._
import duck.collection.SortedListSpec._
import duck.collection.SortedListLemmas._
import duck.proof.MinSpec._
import duck.proof.MinOps._
import duck.proof.MinLemmas._
import leon.annotation._
import leon.collection.ListSpecs._
import leon.collection._
import leon.lang._
import leon.proof._
import SortedListTakeOps._
import SortedListTakeLemmas._
import scala.language.postfixOps
import DeleteSpec._
import DeleteOps._
import DeleteLemmas._

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

  def sort_take_concat_min (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt) : Boolean = {
    require(!l1.isEmpty && !l2.isEmpty && n > 0 && m > 0)
    min(sort(l1).take(n) ++ sort(l2).take(m)) == min(l1 ++ l2) because {
      // min(sort(l1).take(n) ++ sort(l2).take(m))
      // == min(min(sort(l1).take(n)), min(sort(l2).take(m)))
      min_concat_lemma2(sort(l1).take(n), sort(l2).take(m)) &&
      // min(min(l1), min(l2))
      sort_take_min(l1, n) && sort_take_min(l2, m) &&
      // min(l1 ++ l2)
      min_concat_lemma2(l1, l2)
    }
  } holds

  def sort_take_concat_decomp_l (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require (!l1.isEmpty && !l2.isEmpty && n >= r && m >= r && r > 0 && min(l1) <= min(l2))
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ sort(l2).take(m)).take(r - 1) because {
      val min12 = min(sort(l1).take(n) ++ sort(l2).take(m))
      // sort_take(sort(l1).take(n) ++ sort(l2).take(m), r)
      // == min12::sort(delete(sort(l1).take(n) ++ sort(l2).take(m), min12)).take(r - 1)
      sort_take_decomp(sort(l1).take(n) ++ sort(l2).take(m), r) &&
      // == min(l1)::sort(delete(sort(l1).take(n) ++ sort(l2).take(m), min(l1))).take(r - 1)
      sort_take_concat_min(l1, l2, n, m) && min_concat_lemma2(l1, l2) &&
      // == min(l1)::sort(delete(sort(l1).take(n), min(l1)) ++ sort(l2).take(m)).take(r - 1)
      sort_take_min(l1, n) && min_lemma2(sort(l1).take(n)) && delete_concat(sort(l1).take(n), sort(l2).take(m), min(sort(l1).take(n))) &&
      // == min(l1)::sort(delete(sort(l1), min(l1)).take(n - 1) ++ sort(l2).take(m)).take(r - 1)
      sort_take_min(l1, n) && min_lemma2(sort(l1).take(n)) && take_delete(sort(l1), n, min(l1))
    }
  } holds

  def sort_take_concat_decomp_r (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt) : Boolean = {
    require (!l1.isEmpty && !l2.isEmpty && n >= r && m >= r && r > 0 && min(l2) <= min(l1))
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == min(l2)::sort(sort(l1).take(n) ++ sort(delete(l2, min(l2))).take(m - 1)).take(r - 1) because {
      sort_commutative_prop(sort(l1).take(n), sort(l2).take(m)) &&
      sort_take_concat_decomp_l(l2, l1, m, n, r) &&
      sort_commutative_prop(sort(delete(l2, min(l2))).take(m - 1), sort(l1).take(n))
    }
  } holds

  def sort_take_concat_more (l1 : List[BigInt], l2 : List[BigInt], n : BigInt, m : BigInt, r : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(n >= r && m >= r && i >= 0 && j >= 0)
    sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r) == sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r) because {
      if (r <= 0) {
        trivial
      } else if (l1.isEmpty) {
        // sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r)
        leftUnitAppend(sort(l2).take(m)) &&
        // == sort(sort(l2).take(m)).take(r)
        sort_take_sorted(l2, m) && sort_sorted(sort(l2).take(m)) &&
        // == sort(l2).take(min(m, r))
        take_n_m(sort(l2), m, r) &&
        // sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r)
        leftUnitAppend(sort(l2).take(m + j)) &&
        // == sort(sort(l2).take(m + j)).take(r)
        sort_take_sorted(l2, m + j) && sort_sorted(sort(l2).take(m + j)) &&
        // == sort(l2).take(min(m + j, r))
        take_n_m(sort(l2), m + j, r)
      } else if (l2.isEmpty) {
        // sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r)
        sort_commutative_prop(sort(l1).take(n), sort(l2).take(n)) &&
        // == sort(sort(l2).take(m) ++ sort(l1).take(n)).take(r)
        sort_take_concat_more(l2, l1, m, n, r, j, i) &&
        // == sort(sort(l2).take(m + j) ++ sort(l1).take(n + i)).take(r)
        sort_commutative_prop(sort(l2).take(m + j), sort(l1).take(n + i))
      } else if (min(l1) <= min(l2)) {
        // sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r)
        // == min(l1)::sort(sort(delete(l1, min(l1)).take(n - 1) ++ sort(l2).take(m)).take(r - 1)
        sort_take_concat_decomp_l(l1, l2, n, m, r) &&
        // == min(l1)::sort(sort(delete(l1, min(l1)).take(n - 1 + i) ++ sort(l2).take(m + j)).take(r - 1)
        sort_take_concat_more(delete(l1, min(l1)), l2, n - 1, m, r - 1, i, j) &&
        // == sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r)
        sort_take_concat_decomp_l(l1, l2, n + i, m + j, r)
      } else {
        // sort(sort(l1).take(n) ++ sort(l2).take(m)).take(r)
        // == min(l2)::sort(sort(l1).take(n) ++ sort(delete(l2, min(l2)).take(m - 1)).take(r - 1)
        sort_take_concat_decomp_r(l1, l2, n, m, r) &&
        // == min(l2)::sort(sort(l1).take(n + i) ++ sort(delete(l2, min(l2)).take(m - 1 + j)).take(r - 1)
        sort_take_concat_more(l1, delete(l2, min(l2)), n, m - 1, r - 1, i, j) &&
        // == sort(sort(l1).take(n + i) ++ sort(l2).take(m + j)).take(r)
        sort_take_concat_decomp_r(l1, l2, n + i, m + j, r)
      }
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

  def sort_take_concat (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) : Boolean = {
    sort_take(sort_take(l1, n) ++ sort_take(l2, n), n) == sort_take(l1 ++ l2, n) because {
      if (n <= 0) {
        trivial
      } else if (l1.isEmpty) {
        check {
          // sort_take(sort_take(l1, n) ++ sort_take(l2, n), n)
          leftUnitAppend(sort(l2).take(n)) &&
          // == sort(sort(l2).take(n)).take(n)
          sort_take_sorted(l2, n) && sort_sorted(sort(l2).take(n)) &&
          // == sort(l2).take(n).take(n)
          take_n_m(sort(l2), n, n) &&
          // == sort(l2).take(min(n, n)) == sort(l2).take(n)
          // sort_take(l1 ++ l2, n)
          leftUnitAppend(l2)
          // == sort(l2).take(n)
        }
      } else if (l2.isEmpty) {
        check {
          // sort_take(sort_take(l1, n) ++ sort_take(l2, n), n)
          sort_commutative_prop(sort(l1).take(n), sort(l2).take(n)) &&
          // == sort_take(sort_take(l2, n) ++ sort_take(l1, n), n)
          sort_take_concat(l2, l1, n) &&
          // == sort_take(l2 ++ l1, n) &&
          sort_commutative_prop(l2, l1)
          // == sort_take(l1 ++ l2, n)
        }
      } else if (min(l1) <= min(l2)) {
        check {
          // sort_take(sort_take(l1, n) ++ sort_take(l2, n), n)
          sort_take_concat_decomp_l(l1, l2, n, n, n) &&
          // == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ sort(l2).take(n)).take(n - 1)
          sort_take_concat_norm(delete(l1, min(l1)), l2, n - 1, n, n - 1) &&
          // == min(l1)::sort(sort(delete(l1, min(l1))).take(n - 1) ++ sort(l2).take(n - 1)).take(n - 1)
          sort_take_concat(delete(l1, min(l1)), l2, n - 1) &&
          // == min(l1)::sort(delete(l1, min(l1)) ++ l2).take(n - 1)
          delete_concat (l1, l2, min(l1)) && min_lemma2(l1) &&
          // == min(l1)::sort(delete(l1 ++ l2, min(l1))).take(n - 1)
          min_concat_lemma2(l1, l2) && sort_take_decomp(l1 ++ l2, n)
          // == sort_take(l1 ++ l2, n)
        }
      } else {
        check {
          // sort_take(sort_take(l1, n) ++ sort_take(l2, n), n)
          sort_take_concat_decomp_r(l1, l2, n, n, n) &&
          // == min(l2)::sort(sort(l1).take(n) ++ sort(delete(l2, min(l2))).take(n - 1)).take(n - 1)
          sort_take_concat_norm(l1, delete(l2, min(l2)), n, n - 1, n - 1) &&
          // == min(l2)::sort(sort(l1).take(n - 1) ++ sort(delete(l2, min(l2))).take(n - 1)).take(n - 1)
          sort_take_concat(l1, delete(l2, min(l2)), n - 1) &&
          // == min(l2)::sort(l1 ++ delete(l2, min(l2))).take(n - 1)
          min_not_contains(l1, min(l2)) && !l1.contains(min(l2)) && delete_concat_lemma1(l1, l2, min(l2)) &&
          // == min(l2)::sort(delete(l1 ++ l2, min(l2))).take(n - 1)
          min_concat_lemma2(l1, l2) && min(l1 ++ l2) == min(l2) && sort_take_decomp(l1 ++ l2, n)
          // == sort_take(l1 ++ l2, n)
        }
      }
    }
  } holds

  def combOp_comm_lemma (l1: List[BigInt], l2: List[BigInt], n: BigInt) = {
    combOp(l1, l2, n) == combOp(l2, l1, n) because {
      sort_commutative_prop(l1, l2)
    }
  } holds

  @induct
  def combOp_assoc_lemma (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt], n: BigInt) = {
    combOp(combOp(l1, l2, n), l3, n) == combOp(l1, combOp(l2, l3, n), n) because {
      // sort_take(sort_take(l1 ++ l2, n) ++ l3, n)
      sort_take_concat(sort_take(l1 ++ l2, n), l3, n) &&
      // == sort_take(sort_take(sort_take(l1 ++ l2, n), n) ++ sort_take(l3, n), n)
      sort_take_idempotent(l1 ++ l2, n) &&
      // == sort_take(sort_take(l1 ++ l2, n) ++ sort_take(l3, n), n)
      sort_take_concat(l1 ++ l2, l3, n) &&
      // == sort_take((l1 ++ l2) ++ l3, n)
      // sort_take(l1 ++ sort_take(l2 ++ l3, n), n)
      sort_take_concat(l1, sort_take(l2 ++ l3, n), n) &&
      // == sort_take(sort_take(l1, n) ++ sort_take(sort_take(l2 ++ l3, n), n), n)
      sort_take_idempotent(l2 ++ l3, n) &&
      // == sort_take(sort_take(l1, n) ++ sort_take(l2 ++ l3, n), n)
      sort_take_concat(l1, l2 ++ l3, n) &&
      // == sort_take(l1 ++ (l2 ++ l3), n)
      appendAssoc(l1, l2, l3)
      // == sort_take(l1 ++ l2 ++ l3, n)
    }
  } holds
}
