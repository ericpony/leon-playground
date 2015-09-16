package duck.collection

import scala.language.postfixOps
import leon.annotation._
import leon.lang._
import leon.proof._
import KListLemmas._
import SetMapLemmas._
import SetMapOps._

/**
 * Set Map
 * A key-value-set map. Each key corresponds to a set of values.
 * Upon each insertion, the value is add to the set associated with the given key.
 *
 * TODO: prove getAll_perm_lemma
 */
object SetMapSpec {
  @induct
  def insert_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V], key: BigInt): Boolean = {
    equiv((p2 :: p1 :: map).getAll(key), (p1 :: p2 :: map).getAll(key))
  } holds /* verified by Leon */

  def merge_commu_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    equiv((map1 ++ map2).getAll(key), (map2 ++ map1).getAll(key)) because
      merge_perm_lemma(map1, map2, key)
  } holds /* verified by Leon */

  @induct
  def merge_assoc_lemma[V] (map1: KList[V], map2: KList[V], map3: KList[V], key: BigInt): Boolean = {
    equiv((map1 ++ (map2 ++ map3)).getAll(key), ((map1 ++ map2) ++ map3).getAll(key))
  } holds /* verified by Leon */
}

object SetMapOps {
  def equiv[V] (map1: KList[V], map2: KList[V]) = map1.content == map2.content
}

object SetMapLemmas {
  def delete[V] (list: KList[V], e: Item[V]): KList[V] = {
    if (list == Nil[V]()) list
    else if (list.head == e) list.tail
    else Cons(list.head, delete(list.tail, e))
  } ensuring { res =>
    res.size == (if (list contains e) list.size - 1 else list.size) &&
      res.content.subsetOf(list.content)
  } /* verified by Leon */

  def permutation[V] (l1: KList[V], l2: KList[V]): Boolean = {
    if (l1 == Nil[V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res => !res ||
    l1.size == l2.size &&
      permutation(l2, l1) &&
      l1.content.subsetOf(l2.content) &&
      l2.content.subsetOf(l1.content)
  } /* verified by Leon */

  def merge_perm_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    val l1 = map1 ++ map2
    val l2 = map2 ++ map1
    permutation(l1.getAll(key), l2.getAll(key)) because
      permutation_concat_comm(map1, map2) &&
        getAll_perm_lemma(l1, l2, key)
  } holds /* verified by Leon */

  def getAll_perm_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    val l1 = map1.getAll(key)
    val l2 = map2.getAll(key)
    if (l1 == Nil[V]())
      l2 == Nil[V]() && permutation(l1, l2)
    else {
      val h1 = l1.head
      permutation(l1, l2) because
        check {
          //          check { l2.contains(h1) because getAll_contain_lemma(map1, map2, key) } &&
          //            check { permutation(l1.tail, delete(l2, h1)) because
          //              getAll_perm_lemma(map1.deleteFirst(key), map2.deleteFirst(key), key) } &&
          check {
            permutation(l1.tail, delete(l2, h1)) because
              permutation_delete(map1, map2, h1) &&
                getAll_perm_lemma(delete(map1, h1), delete(map2, h1), key)
          } && permutation(l1.tail, delete(l2, h1)) &&
            permutation_prefix(l1.tail, delete(l2, h1), h1) &&
            permutation(l1, h1 :: delete(l2, h1)) &&
            permutation(h1 :: delete(l2, h1), l2) &&
            permutation_tran(l1, h1 :: delete(l2, h1), l2)
        }
    }
  } holds /* timeout */
}

object KListLemmas {
  /* verified by Leon */
  @induct
  def permutation_refl[V] (list: KList[V]): Boolean = {
    permutation(list, list)
  } holds

  def permutation_comm[V] (l1: KList[V], l2: KList[V]): Boolean = {
    require(permutation(l1, l2))
    permutation(l2, l1) because permutation_comm_lemma(l1, l2)
  } holds

  def permutation_tran[V] (l1: KList[V], l2: KList[V], l3: KList[V]): Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    permutation(l1, l3) because permutation_tran_lemma(l1, l2, l3)
  } holds

  def permutation_content[V] (l1: KList[V], l2: KList[V]): Boolean = {
    require(permutation(l1, l2))
    l1.content == l2.content because permutation_content_lemma(l1, l2)
  } holds

  def permutation_concat[V] (l1: KList[V], l2: KList[V], ll: KList[V]) = {
    require(permutation(l1, l2))
    permutation(l1 ++ ll, l2 ++ ll) because
      permutation_concat_lemma(l1, l2, ll)
  } holds

  def permutation_concat_comm[V] (l1: KList[V], l2: KList[V]): Boolean = {
    permutation(l1 ++ l2, l2 ++ l1) because
      permutation_concat_comm_lemma(l1, l2)
  } holds

  def permutation_concat_assoc[V] (l1: KList[V], l2: KList[V], l3: KList[V]) = {
    permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
      permutation_concat_assoc_lemma(l1, l2, l3)
  } holds

  @induct
  def permutation_car_swap[V] (list: KList[V], a: Item[V], b: Item[V]): Boolean = {
    permutation(a :: b :: list, b :: a :: list)
  } holds

  @induct
  def permutation_cons_tail[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    if (l1 == Nil[V]()) {
      permutation(l1 ++ (e :: l2), (e :: l1) ++ l2) because
        permutation_refl(e :: l2)
    } else {
      val h1 = l1.head
      permutation(l1 ++ (e :: l2), (e :: l1) ++ l2) because
        check {
          // permutation (l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2)
          permutation_cons_tail(l1.tail, l2, e) &&
            // permutation (h1 :: (l1.tail ++ (e :: l2)), h1 :: (e :: l1.tail) ++ l2)
            permutation_cons(l1.tail ++ (e :: l2), (e :: l1.tail) ++ l2, h1) &&
            // permutation (h1 :: e :: l1.tail ++ l2, e :: h1 :: l1.tail ++ l2)
            permutation_car_swap(l1.tail ++ l2, h1, e) &&
            permutation_tran_lemma(l1 ++ (e :: l2),
              h1 :: e :: l1.tail ++ l2,
              (e :: l1) ++ l2)
        }
    }
  } holds

  @induct
  def permutation_cons_delete[V] (l1: KList[V], l2: KList[V]): Boolean = {
    require(l2 != Nil[V]())
    val h2 = l2.head
    if (l1 == Nil[V]) {
      permutation(delete(l1 ++ l2, h2), l1 ++ (l2.tail)) because
        permutation_refl(l2.tail)
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation(delete(l1 ++ l2, h2), l1 ++ (l2.tail)) because
          permutation_cons_tail(l1.tail, l2.tail, h1)
      } else {
        permutation(delete(l1 ++ l2, h2), l1 ++ (l2.tail)) because
          permutation_cons_delete(l1.tail, l2)
      }
    }
  } holds

  @induct
  private def permutation_concat_comm_lemma[V] (l1: KList[V], l2: KList[V]): Boolean = {
    if (l1 == Nil[V]()) {
      permutation(l1 ++ l2, l2 ++ l1) because
        permutation_refl(l2)
    } else {
      val h1 = l1.head
      permutation(l1 ++ l2, l2 ++ l1) because
        check {
          (l2 ++ l1 contains h1) &&
            // permutation (l1.tail ++ l2, l2 ++ l1.tail)
            permutation_concat_comm(l1.tail, l2) &&
            (l1 ++ l2).tail == l1.tail ++ l2 &&
            // permutation (delete (l2 ++ l1, h1), l2 ++ l1.tail)
            permutation_cons_delete(l2, l1) &&
            // permutation (l2 ++ l1.tail, delete (l2 ++ l1, h1))
            permutation_comm_lemma(delete(l2 ++ l1, h1), l2 ++ l1.tail) &&
            permutation_tran_lemma(l1.tail ++ l2, l2 ++ l1.tail, delete(l2 ++ l1, h1))
        }
    }
  } holds

  @induct
  def permutation_delete_head[V] (t1: KList[V], l2: KList[V], h1: Item[V]): Boolean = {
    require(permutation(h1 :: t1, l2))
    permutation(t1, delete(l2, h1))
  } holds

  @induct
  def permutation_delete[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == Nil[V]()) {
      permutation(delete(l1, e), delete(l2, e))
    } else {
      val h1 = l1.head
      if (e == h1) {
        permutation(delete(l1, h1), delete(l2, h1)) because
          permutation_delete_head(l1.tail, l2, h1)
      } else {
        permutation(delete(l1, e), delete(l2, e)) because
          check {
            delete_contains(l2, h1, e) &&
              permutation_delete(l1.tail, delete(l2, h1), e) &&
              delete_comm(l2, e, h1)
          }
      }
    }
  } holds

  @induct
  def permutation_cons_delete[V] (l1: KList[V], h2: Item[V], t2: KList[V]): Boolean = {
    require(permutation(delete(l1, h2), t2) && l1.contains(h2))
    if (l1 == Nil[V]()) {
      permutation(l1, Cons(h2, t2))
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation(l1, Cons(h2, t2))
      } else {
        permutation(l1, Cons(h2, t2)) because
          check {
            (Cons(h2, t2) contains h1) &&
              delete_comm(l1, h1, h2) &&
              permutation_cons_delete(l1.tail, h2, delete(t2, h1))
          }
      }
    }
  } holds

  @induct
  def permutation_comm_lemma[V] (l1: KList[V], l2: KList[V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == Nil[V]()) {
      permutation(l2, l1)
    } else {
      permutation(l2, l1) because
        check {
          permutation_content(l1, l2) &&
            l1.contains(l2.head) &&
            permutation_comm(l1.tail, delete(l2, l1.head)) &&
            permutation_cons_delete(l2, l1.head, l1.tail) &&
            permutation_delete(l2, l1, l2.head)
        }
    }
  } holds

  @induct
  def permutation_tran_lemma[V] (l1: KList[V], l2: KList[V], l3: KList[V]): Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    if (l1 == Nil[V]()) {
      permutation(l1, l3)
    } else {
      val h1 = l1.head
      permutation(l1, l3) because
        // l3 contains h1
        permutation_contains_lemma(l2, l3, h1) &&
          // permutation (delete (l2, h1), delete (l3, h1))
          permutation_delete(l2, l3, h1) &&
          // permutation (l1.tail, delete (l3, h1))
          permutation_tran_lemma(l1.tail, delete(l2, h1), delete(l3, h1))
    }
  } holds

  @induct
  def permutation_cons[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    require(permutation(l1, l2))
    permutation(Cons(e, l1), Cons(e, l2))
  } holds

  @induct
  def permutation_content_lemma[V] (l1: KList[V], l2: KList[V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == Nil[V]()) {
      l1.content == l2.content
    } else {
      val h1 = l1.head
      l1.content == l2.content because
        l1.content == l1.tail.content ++ Set(h1) &&
          l2.content == delete(l2, h1).content ++ Set(h1) &&
          check { delete_content(l2, h1) } &&
          check { permutation_content_lemma(l1.tail, delete(l2, h1)) }
    }
  } holds

  def permutation_contains_lemma[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    require(permutation(l1, l2) && l1.contains(e))
    val h = l1.head
    if (h == e) {
      l2.contains(e)
    } else {
      /* induction */
      l2.contains(e) because {
        check { permutation_contains_lemma(l1.tail, delete(l2, h), e) }
      }
    }
  } holds

  @induct
  def permutation_prefix[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    require(permutation(l1, l2))
    permutation(Cons(e, l1), Cons(e, l2))
  } holds

  @induct
  private def permutation_concat_lemma[V] (l1: KList[V], l2: KList[V], ll: KList[V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == Nil[V]()) {
      permutation(l1 ++ ll, l2 ++ ll) because
        check { permutation_refl(ll) }
    } else {
      val h1 = l1.head
      permutation(l1 ++ ll, l2 ++ ll) because
        check {
          permutation_concat_lemma(l1.tail, delete(l2, h1), ll) &&
            l1.tail ++ ll == (l1 ++ ll).tail &&
            delete(l2, h1) ++ ll == delete(l2 ++ ll, h1) &&
            delete_concat(l2, ll, h1)
        }
    }
  } holds

  @induct
  private def permutation_concat_assoc_lemma[V] (l1: KList[V], l2: KList[V], l3: KList[V]): Boolean = {
    if (l1 == Nil[V]()) {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_refl(l2 ++ l3)
    } else {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_concat_assoc_lemma(l1.tail, l2, l3) &&
          permutation_cons(l1.tail ++ l2 ++ l3, l1.tail ++ (l2 ++ l3), l1.head)
    }
  } holds

  def concat_permutation[V] (ll: KList[V], l1: KList[V], l2: KList[V]) = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      concat_permutation_lemma(ll, l1, l2)
  } holds

  def concat_permutation_lemma[V] (ll: KList[V], l1: KList[V], l2: KList[V]): Boolean = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      // permutation (l1 ++ ll, l2 ++ ll)
      permutation_concat_lemma(l1, l2, ll) &&
        // permutation (ll ++ l1, l1 ++ ll)
        permutation_concat_comm_lemma(ll, l1) &&
        // permutation (l2 ++ ll, ll ++ l2)
        permutation_concat_comm_lemma(l2, ll) &&
        permutation_tran_lemma(ll ++ l1, l1 ++ ll, l2 ++ ll) &&
        permutation_tran_lemma(ll ++ l1, l2 ++ ll, ll ++ l2)
  } holds

  @induct
  def delete_permutation[V] (list: KList[V], e: Item[V]): Boolean = {
    require(list contains e)
    val h = list.head
    if (h == e) {
      permutation(list, Cons(e, delete(list, e))) because
        permutation_refl(list)
    } else {
      permutation(list, Cons(e, delete(list, e))) because
        delete(list, e) == Cons(h, delete(list.tail, e))
    }
  } holds

  @induct
  def delete_contains[V] (list: KList[V], a: Item[V], b: Item[V]) = {
    require(list.contains(a) && a != b)
    delete(list, b).contains(a)
  } holds

  @induct
  def delete_content[V] (list: KList[V], e: Item[V]): Boolean = {
    require(list.contains(e))
    list.content == delete(list, e).content ++ Set(e)
  } holds

  @induct
  def delete_concat[V] (l1: KList[V], l2: KList[V], e: Item[V]): Boolean = {
    require(l1 contains e)
    delete(l1, e) ++ l2 == delete(l1 ++ l2, e)
  } holds

  @induct
  def delete_comm[V] (list: KList[V], a: Item[V], b: Item[V]): Boolean = {
    delete(delete(list, a), b) == delete(delete(list, b), a)
  } holds

}
