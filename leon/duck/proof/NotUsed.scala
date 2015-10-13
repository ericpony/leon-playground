package duck.proof

import duck.proof.sugar._
import duck.collection._

import leon.annotation._
import leon.lang._
import leon.proof._

import MinOps._
import MinSpec._
import DeleteSpec._
import DeleteOps._
import PermutationSpec._
import PermutationOps._
import PermutationLemmas._

object NotUsed {

  @induct
  def permutation_min (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(permutation(l1, l2) && l1 != Nil[BigInt]())
    min(l1) == min(l2) because
      check { permutation_content_lemma(l1, l2) } &&
        check { min_content(l1, l2) }
  } holds
}
