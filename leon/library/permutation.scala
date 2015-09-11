import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import MinSpec._
import MinOps._
import DeleteSpec._
import DeleteOps._
import PermutationSpec._
import PermutationOps._
import PermutationLemmas._
import scala.language.postfixOps

object PermutationSpec {
  @induct
  def permutation_refl (list : List[BigInt]) : Boolean = {
    permutation (list, list)
  } holds

  def permutation_comm (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    permutation (l2, l1) because permutation_comm_lemma (l1, l2)
  } holds

  def permutation_tran (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2) && permutation (l2, l3))
    permutation (l1, l3) because permutation_tran_lemma (l1, l2, l3)
  } holds

  def permutation_content (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    l1.content == l2.content because permutation_content_lemma (l1, l2)
  } holds

  /* Proven in the post-condition of `permutation` */
//  def permutation_size (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
//    require (permutation (l1, l2))
//    l1.size == l2.size because permutation_size_lemma (l1, l2)
//  } holds

  def permutation_concat (l1 : List[BigInt], l2 : List[BigInt], ll : List[BigInt]) = {
    require (permutation (l1, l2))
    permutation (l1 ++ ll, l2 ++ ll) because
      permutation_concat_lemma (l1, l2, ll)
  } holds

  def concat_permutation (ll : List[BigInt], l1 : List[BigInt], l2 : List[BigInt]) = {
    require (permutation (l1, l2))
    permutation (ll ++ l1, ll ++ l2) because
      concat_permutation_lemma (ll, l1, l2)
  } holds

  def permutation_concat_comm (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    permutation (l1 ++ l2, l2 ++ l1) because
      permutation_concat_comm_lemma (l1, l2)
  } holds

  def permutation_concat_assoc (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) = {
    permutation (l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
      permutation_concat_assoc_lemma (l1, l2, l3)
  } holds
}

object PermutationOps {
  /**
   * Tell whether a list is a permutation of the other
   * @param l1, l2 are lists
   * @return whether l1 is a permutation of l2
   */
  def permutation (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    if (l1 == Nil[BigInt]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains (h1) && permutation (l1.tail, delete (l2, h1))
    }
  } ensuring { res => !res ||
    l1.size == l2.size &&
    permutation(l2, l1) &&
    l1.content.subsetOf(l2.content) &&
    l2.content.subsetOf(l1.content)
  }
}

object PermutationLemmas {
  @induct
  def permutation_car_swap (list : List[BigInt], a : BigInt, b : BigInt) : Boolean = {
    permutation (a :: b :: list, b :: a :: list)
  } holds

  @induct
  def permutation_cons_tail (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    if (l1 == Nil[BigInt]()) {
      permutation (l1 ++ (e :: l2), (e :: l1) ++ l2) because
      check { permutation_refl (e :: l2) }
    } else {
      val h1 = l1.head
      permutation (l1 ++ (e :: l2), (e :: l1) ++ l2) because
      check {
        // permutation (l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2)
        permutation_cons_tail (l1.tail, l2, e) &&
        // permutation (h1 :: (l1.tail ++ (e :: l2)), h1 :: (e :: l1.tail) ++ l2)
        permutation_cons (l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2, h1) &&
        // permutation (h1 :: e :: l1.tail ++ l2, e :: h1 :: l1.tail ++ l2)
        permutation_car_swap (l1.tail ++ l2, h1, e) &&
        permutation_tran_lemma (l1 ++ (e :: l2),
                                h1 :: e :: l1.tail ++ l2,
                                (e :: l1) ++ l2)
      }
    }
  } holds

  @induct
  def permutation_cons_delete (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (l2 != Nil[BigInt]())
    val h2 = l2.head
    if (l1 == Nil[BigInt]) {
      permutation (delete (l1 ++ l2, h2), l1 ++ (l2.tail)) because
      check { permutation_refl (l2.tail) }
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation (delete (l1 ++ l2, h2), l1 ++ (l2.tail)) because
        check {
          permutation_cons_tail (l1.tail, l2.tail, h1)
        }
      } else {
        permutation (delete (l1 ++ l2, h2), l1 ++ (l2.tail)) because
        check {
          permutation_cons_delete (l1.tail, l2)
        }
      }
    }
  } holds

  @induct
  def permutation_concat_comm_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    if (l1 == Nil[BigInt]()) {
      permutation (l1 ++ l2, l2 ++ l1) because
        permutation_refl (l2)
    } else {
      val h1 = l1.head
      permutation (l1 ++ l2, l2 ++ l1) because
      check {
        (l2 ++ l1 contains h1) &&
        // permutation (l1.tail ++ l2, l2 ++ l1.tail)
        permutation_concat_comm (l1.tail, l2) &&
        (l1 ++ l2).tail == l1.tail ++ l2 &&
        // permutation (delete (l2 ++ l1, h1), l2 ++ l1.tail)
        permutation_cons_delete (l2, l1) &&
        // permutation (l2 ++ l1.tail, delete (l2 ++ l1, h1))
        permutation_comm_lemma (delete (l2 ++ l1, h1), l2 ++ l1.tail) &&
        permutation_tran_lemma (l1.tail ++ l2, l2 ++ l1.tail, delete (l2 ++ l1, h1))
      }
    }
  } holds

  @induct
  def permutation_delete_head (t1 : List[BigInt], l2 : List[BigInt], h1 : BigInt) : Boolean = {
    require (permutation (h1 :: t1, l2))
      permutation (t1, delete (l2, h1))
  } holds

  @induct
  def permutation_delete (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require (permutation (l1, l2))
    if (l1 == Nil[BigInt]()) {
      permutation (delete (l1, e), delete (l2, e))
    } else {
      val h1 = l1.head
      if (e == h1) {
        permutation (delete (l1, h1), delete (l2, h1)) because
        permutation_delete_head (l1.tail, l2, h1)
      } else {
        permutation (delete (l1, e), delete (l2, e)) because
        check { delete_contains (l2, h1, e) &&
          permutation_delete (l1.tail, delete (l2, h1), e) &&
          delete_comm (l2, e, h1)
        }
      }
    }
  } holds

  @induct
  def permutation_cons_delete (l1 : List[BigInt], h2 : BigInt, t2 : List[BigInt]) : Boolean = {
    require (permutation (delete (l1, h2), t2) && l1.contains (h2))
    if (l1 == Nil[BigInt]()) {
      permutation (l1, Cons (h2, t2))
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation (l1, Cons (h2, t2))
      } else {
        permutation (l1, Cons (h2, t2)) because
        check { (Cons (h2, t2) contains h1) &&
                delete_comm (l1, h1, h2) &&
                permutation_cons_delete (l1.tail, h2, delete (t2, h1))
        }
      }
    }
  } holds

  @induct
  def permutation_comm_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    if (l1 == Nil[BigInt]()) {
      permutation (l2, l1)
    } else {
      permutation (l2, l1) because
      check { permutation_content (l1, l2) &&
              l1.contains (l2.head) &&
              permutation_comm (l1.tail, delete (l2, l1.head)) &&
              permutation_cons_delete (l2, l1.head, l1.tail) &&
              permutation_delete (l2, l1, l2.head)
      }
    }
  } holds

  @induct
  def permutation_tran_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2) && permutation (l2, l3))
    if (l1 == Nil[BigInt]()) {
      permutation (l1, l3)
    } else {
      val h1 = l1.head
      permutation (l1, l3) because
      check {
        // l3 contains h1
        permutation_contains_lemma (l2, l3, h1) &&
        // permutation (delete (l2, h1), delete (l3, h1))
        permutation_delete (l2, l3, h1) &&
        // permutation (l1.tail, delete (l3, h1))
        permutation_tran_lemma (l1.tail, delete (l2, h1), delete (l3, h1))
      }
    }
  } holds

  @induct
  def permutation_cons (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require (permutation (l1, l2))
    permutation (Cons (e, l1), Cons (e, l2))
  } holds

    /* Proven in the post-condition of `permutation` */
//  @induct
//  def permutation_size_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
//    require (permutation (l1, l2))
//    if (l1 == Nil[BigInt]()) {
//      l1.size == l2.size
//    } else {
//      l1.size == l2.size because
//      check {
//        permutation_size_lemma (l1.tail, delete (l2, l1.head))
//      }
//    }
//  } holds

  @induct
  def permutation_content_lemma (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    if (l1 == Nil[BigInt]()) {
      l1.content == l2.content
    } else {
      val h1 = l1.head
      l1.content == l2.content because
        l1.content == l1.tail.content ++ Set (h1) &&
        l2.content == delete (l2, h1).content ++ Set (h1) &&
        check { delete_content (l2, h1) } &&
        check { permutation_content_lemma (l1.tail, delete (l2, h1)) }
    }
  } holds

  @induct
  def permutation_contains_lemma (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require (permutation (l1, l2) && l1.contains (e))
    val h = l1.head
    if (h == e) {
      l2.contains (e)
    } else {
      /* induction */
      l2.contains (e) because {
        check { permutation_contains_lemma (l1.tail, delete (l2, h), e) }
      }
    }
  } holds

  @induct
  def permutation_min (l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2) && l1 != Nil[BigInt]())
    min (l1) == min (l2) because
      check { permutation_content_lemma (l1, l2) } &&
      check { min_content (l1, l2) }
  } holds

  @induct
  def permutation_prefix (l1 : List[BigInt], l2 : List[BigInt], e : BigInt) : Boolean = {
    require (permutation (l1, l2))
    permutation (Cons (e, l1), Cons (e, l2))
  } holds

  @induct
  def permutation_concat_lemma (l1 : List[BigInt], l2 : List[BigInt], ll : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    if (l1 == Nil[BigInt]()) {
      permutation (l1 ++ ll, l2 ++ ll) because
        check { permutation_refl (ll) }
    } else {
      val h1 = l1.head
      permutation (l1 ++ ll, l2 ++ ll) because
        check {
          permutation_concat_lemma (l1.tail, delete (l2, h1), ll) &&
          l1.tail ++ ll == (l1 ++ ll).tail &&
          delete (l2, h1) ++ ll == delete (l2 ++ ll, h1) &&
          delete_concat (l2, ll, h1)
        }
    }
  } holds

  def concat_permutation_lemma (ll : List[BigInt], l1 : List[BigInt], l2 : List[BigInt]) : Boolean = {
    require (permutation (l1, l2))
    permutation (ll ++ l1, ll ++ l2) because
      // permutation (l1 ++ ll, l2 ++ ll)
      permutation_concat_lemma (l1, l2, ll) &&
      // permutation (ll ++ l1, l1 ++ ll)
      permutation_concat_comm_lemma (ll, l1) &&
      // permutation (l2 ++ ll, ll ++ l2)
      permutation_concat_comm_lemma (l2, ll) &&
      permutation_tran_lemma (ll ++ l1, l1 ++ ll, l2 ++ ll) &&
      permutation_tran_lemma (ll ++ l1, l2 ++ ll, ll ++ l2)
  } holds

  @induct
  def delete_permutation (list : List[BigInt], e : BigInt) : Boolean = {
    require (list contains e)
    val h = list.head
    if (h == e) {
      permutation (list, Cons (e, delete (list, e))) because
        permutation_refl (list)
    } else {
      permutation (list, Cons (e, delete (list, e))) because
        delete (list, e) == Cons (h, delete (list.tail, e))
    }
  } holds

  @induct
  def permutation_concat_assoc_lemma (l1 : List[BigInt], l2 : List[BigInt], l3 : List[BigInt]) : Boolean = {
    if (l1 == Nil[BigInt]()) {
      permutation (l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_refl (l2 ++ l3)
    } else {
      permutation (l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_concat_assoc_lemma (l1.tail, l2, l3) &&
        permutation_cons (l1.tail ++ l2 ++ l3, l1.tail ++ (l2 ++ l3), l1.head)
    }
  } holds
}
