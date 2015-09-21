package duck.proof

import duck.proof.PermutationSpec._
import duck.collection.SortedListOps._
import duck.collection.SortedListSpec._
import duck.collection.SortedListLemmas._
import duck.proof.MinOps._
import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._
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

  def combOp_comm_lemma (l1: List[BigInt], l2: List[BigInt], n: BigInt) = {
    combOp(l1, l2, n) == combOp(l2, l1, n) because {
      sort_commutative_prop(l1, l2)
    }
  } holds

  @induct
  def combOp_assoc_lemma (l1: List[BigInt], l2: List[BigInt], l3: List[BigInt], n: BigInt) = {
    combOp(combOp(l1, l2, n), l3, n) == combOp(l1, combOp(l2, l3, n), n)
  } holds
}
