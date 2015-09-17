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
import SortedListSpec._
import SortedListTakeOps._
import SortedListTakeLemmas._
import scala.language.postfixOps

object SortedListTakeSpec {
  def combOp_comm (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    combOp (l1, l2, n) == combOp (l2, l1, n) because
      combOp_comm_lemma (l1, l2, n)
  } holds
}

object SortedListTakeOps {
  def sort_take (list : List[BigInt], n : BigInt) : List[BigInt] = {
    sort (list).take (n)
  } ensuring {
    res => isSorted (res) && res.size == (
      if (n <= 0) BigInt(0)
      else if (n > list.size) list.size
      else n
    )
  }

  def seqOp (list : List[BigInt], e : BigInt, n : BigInt) = {
    sort_take (e::list, n)
  }

  def combOp (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    sort_take (l1 ++ l2, n)
  }
}

object SortedListTakeLemmas {
  @induct
  def combOp_comm_lemma (l1 : List[BigInt], l2 : List[BigInt], n : BigInt) = {
    combOp (l1, l2, n) == combOp (l2, l1, n) because {
      permutation_concat_comm (l1, l2) &&
      sort_permutation_prop (l1 ++ l2, l2 ++ l1)
    }
  } holds

  @induct
  def combOp_assoc_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt], n : BigInt) = {
    combOp (combOp (l1, l2, n), l3, n) == combOp (l1, combOp (l2, l3, n), n)
  } holds
}
