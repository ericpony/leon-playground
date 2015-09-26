package duck.proof

import duck.proof.sugar._
import duck.collection.KList._
import leon.annotation._
import leon.lang._
import leon.proof._

import scala.language.postfixOps

@library
object KListLemmas {

  @induct
  def permutation_refl[K, V] (list: KList[K, V]): Boolean = {
    permutation(list, list)
  } holds

  def permutation_comm[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    require(permutation(l1, l2))
    permutation(l2, l1) because permutation_comm_lemma(l1, l2)
  } holds

  def permutation_tran[K, V] (l1: KList[K, V], l2: KList[K, V], l3: KList[K, V]): Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    permutation(l1, l3) because permutation_tran_lemma(l1, l2, l3)
  } holds

  def permutation_content[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    require(permutation(l1, l2))
    l1.content == l2.content because permutation_content_lemma(l1, l2)
  } holds

  def permutation_concat[K, V] (l1: KList[K, V], l2: KList[K, V], ll: KList[K, V]) = {
    require(permutation(l1, l2))
    permutation(l1 ++ ll, l2 ++ ll) because
      permutation_concat_lemma(l1, l2, ll)
  } holds

  def permutation_concat_comm[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    permutation(l1 ++ l2, l2 ++ l1) because
      permutation_concat_comm_lemma(l1, l2)
  } holds

  def permutation_concat_assoc[K, V] (l1: KList[K, V], l2: KList[K, V], l3: KList[K, V]) = {
    permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
      permutation_concat_assoc_lemma(l1, l2, l3)
  } holds

  @induct
  def permutation_car_swap[K, V] (list: KList[K, V], a: Item[K, V], b: Item[K, V]): Boolean = {
    permutation(a :: b :: list, b :: a :: list)
  } holds

  @induct
  def permutation_cons_tail[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    if (l1 == KNil[K, V]()) {
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
  def permutation_cons_delete[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    require(l2 != KNil[K, V]())
    val h2 = l2.head
    if (l1 == KNil[K, V]) {
      permutation((l1 ++ l2).delete(h2), l1 ++ (l2.tail)) because
        permutation_refl(l2.tail)
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation((l1 ++ l2).delete(h2), l1 ++ (l2.tail)) because
          permutation_cons_tail(l1.tail, l2.tail, h1)
      } else {
        permutation((l1 ++ l2).delete(h2), l1 ++ (l2.tail)) because
          permutation_cons_delete(l1.tail, l2)
      }
    }
  } holds

  @induct
  private def permutation_concat_comm_lemma[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    if (l1 == KNil[K, V]()) {
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
            permutation_comm_lemma((l2 ++ l1).delete(h1), l2 ++ l1.tail) &&
            permutation_tran_lemma(l1.tail ++ l2, l2 ++ l1.tail, (l2 ++ l1).delete(h1))
        }
    }
  } holds

  @induct
  def permutation_delete_head[K, V] (t1: KList[K, V], l2: KList[K, V], h1: Item[K, V]): Boolean = {
    require(permutation(h1 :: t1, l2))
    permutation(t1, delete(l2, h1))
  } holds

  @induct
  def permutation_delete[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == KNil[K, V]()) {
      permutation(l1.delete(e), l2.delete(e))
    } else {
      val h1 = l1.head
      if (e == h1) {
        permutation(l1.delete(h1), l2.delete(h1)) because
          permutation_delete_head(l1.tail, l2, h1)
      } else {
        permutation(l1.delete(e), l2.delete(e)) because
          check {
            delete_contains(l2, h1, e) &&
              permutation_delete(l1.tail, l2.delete(h1), e) &&
              delete_comm(l2, e, h1)
          }
      }
    }
  } holds

  @induct
  def permutation_cons_delete[K, V] (l1: KList[K, V], h2: Item[K, V], t2: KList[K, V]): Boolean = {
    require(permutation(l1.delete(h2), t2) && l1.contains(h2))
    if (l1 == KNil[K, V]()) {
      permutation(l1, KCons(h2, t2))
    } else {
      val h1 = l1.head
      if (h1 == h2) {
        permutation(l1, KCons(h2, t2))
      } else {
        permutation(l1, KCons(h2, t2)) because
          check {
            (KCons(h2, t2) contains h1) &&
              delete_comm(l1, h1, h2) &&
              permutation_cons_delete(l1.tail, h2, t2 delete h1)
          }
      }
    }
  } holds

  @induct
  def permutation_comm_lemma[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == KNil[K, V]()) {
      permutation(l2, l1)
    } else {
      permutation(l2, l1) because
        check {
          permutation_content(l1, l2) &&
            l1.contains(l2.head) &&
            permutation_comm(l1.tail, l2 delete l1.head) &&
            permutation_cons_delete(l2, l1.head, l1.tail) &&
            permutation_delete(l2, l1, l2.head)
        }
    }
  } holds

  @induct
  def permutation_tran_lemma[K, V] (l1: KList[K, V], l2: KList[K, V], l3: KList[K, V]): Boolean = {
    require(permutation(l1, l2) && permutation(l2, l3))
    if (l1 == KNil[K, V]()) {
      permutation(l1, l3)
    } else {
      val h1 = l1.head
      permutation(l1, l3) because
        // l3 contains h1
        permutation_contains_lemma(l2, l3, h1) &&
          // permutation (delete (l2, h1), delete (l3, h1))
          permutation_delete(l2, l3, h1) &&
          // permutation (l1.tail, delete (l3, h1))
          permutation_tran_lemma(l1.tail, l2 delete h1, l3 delete h1)
    }
  } holds

  @induct
  def permutation_cons[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    require(permutation(l1, l2))
    permutation(KCons(e, l1), KCons(e, l2))
  } holds

  @induct
  def permutation_content_lemma[K, V] (l1: KList[K, V], l2: KList[K, V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == KNil[K, V]()) {
      l1.content == l2.content
    } else {
      val h1 = l1.head
      l1.content == l2.content because
        l1.content == l1.tail.content ++ Set(h1) &&
          l2.content == l2.delete(h1).content ++ Set(h1) &&
          check { delete_content(l2, h1) } &&
          check { permutation_content_lemma(l1.tail, l2.delete(h1)) }
    }
  } holds

  def permutation_contains_lemma[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    require(permutation(l1, l2) && l1.contains(e))
    val h = l1.head
    if (h == e) {
      l2.contains(e)
    } else {
      /* induction */
      l2.contains(e) because {
        check { permutation_contains_lemma(l1.tail, l2 delete h, e) }
      }
    }
  } holds

  @induct
  def permutation_prefix[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    require(permutation(l1, l2))
    permutation(KCons(e, l1), KCons(e, l2))
  } holds

  @induct
  private def permutation_concat_lemma[K, V] (l1: KList[K, V], l2: KList[K, V], ll: KList[K, V]): Boolean = {
    require(permutation(l1, l2))
    if (l1 == KNil[K, V]()) {
      permutation(l1 ++ ll, l2 ++ ll) because
        check { permutation_refl(ll) }
    } else {
      val h1 = l1.head
      permutation(l1 ++ ll, l2 ++ ll) because
        check {
          permutation_concat_lemma(l1.tail, l2.delete(h1), ll) &&
            l1.tail ++ ll == (l1 ++ ll).tail &&
            l2.delete(h1) ++ ll == (l2 ++ ll).delete(h1) &&
            delete_concat(l2, ll, h1)
        }
    }
  } holds

  @induct
  private def permutation_concat_assoc_lemma[K, V] (l1: KList[K, V], l2: KList[K, V], l3: KList[K, V]): Boolean = {
    if (l1 == KNil[K, V]()) {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_refl(l2 ++ l3)
    } else {
      permutation(l1 ++ l2 ++ l3, l1 ++ (l2 ++ l3)) because
        permutation_concat_assoc_lemma(l1.tail, l2, l3) &&
          permutation_cons(l1.tail ++ l2 ++ l3, l1.tail ++ (l2 ++ l3), l1.head)
    }
  } holds

  def permutation_hasKey_lemma[K, V] (map1: KList[K, V], map2: KList[K, V], key: K): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) iff map2.hasKey(key) because {
      permutation_hasKey_lemma2(map1, map2, key) &&
        permutation_hasKey_lemma2(map2, map1, key)
    }
  } holds /* verified by Leon */

  /* This lemma is only used in permutation_hasKey_lemma */
  @induct
  def permutation_hasKey_lemma2[K, V] (map1: KList[K, V], map2: KList[K, V], key: K): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) implies map2.hasKey(key) because {
      !map1.hasKey(key) || map2.contains(map1.get(key).get)
    }
  } holds /* verified by Leon */

  /**
   * WARNING: Leon may take 2~30 seconds to verify this lemma.
   **/
  def permutation_getAll_lemma[K, V] (map1: KList[K, V], map2: KList[K, V], key: K): Boolean = {
    require(permutation(map1, map2))
    val l1 = map1.getAll(key)
    val l2 = map2.getAll(key)

    permutation(l1, l2) because {
      if (l1 == KNil[K, V]())
        permutation(l1, l2) because
          l1 == KNil[K, V]() iff !l1.hasKey(key) &&
          l2 == KNil[K, V]() iff !l2.hasKey(key) &&
          permutation_hasKey_lemma(map1, map2, key)
      else {
        val h1 = map1.get(key).get
        val m1 = map1.delete(h1)
        val m2 = map2.delete(h1)
        l1.head == h1 &&
          check {
            l2.contains(h1) because
              getAll_contain_lemma(map2, h1)
          } &&
          check {
            permutation(m1, m2) because
              permutation_delete(map1, map2, h1)
          } &&
          check {
            permutation(m1.getAll(key), m2.getAll(key)) because
              permutation_getAll_lemma(m1, m2, key)
          } &&
          check { m1.getAll(key) == l1.tail because getAll_delete_lemma(map1, h1, key) } &&
          check { m2.getAll(key) == l2.delete(h1) because getAll_delete_lemma(map2, h1, key) } &&
          permutation(l2.delete(h1), l1.tail) &&
          permutation_cons_delete(l2, h1, l1.tail)
      }
    }
  } holds /* verified by Leon */

  @induct
  def getAll_delete_lemma[K, V] (map: KList[K, V], e: Item[K, V], key: K): Boolean = {
    require(map.contains(e) && e.key == key)
    map.delete(e).getAll(key) == map.getAll(key).delete(e)
  } holds /* verified by Leon */

  @induct
  def getAll_contain_lemma[K, V] (map: KList[K, V], e: Item[K, V]): Boolean = {
    require(map contains e)
    map.getAll(e.key) contains e
  } holds /* verified by Leon */

  def concat_permutation[K, V] (ll: KList[K, V], l1: KList[K, V], l2: KList[K, V]) = {
    require(permutation(l1, l2))
    permutation(ll ++ l1, ll ++ l2) because
      concat_permutation_lemma(ll, l1, l2)
  } holds

  def concat_permutation_lemma[K, V] (ll: KList[K, V], l1: KList[K, V], l2: KList[K, V]): Boolean = {
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
  def permutation_cons_delete[K, V] (list: KList[K, V], e: Item[K, V]): Boolean = {
    require(list contains e)
    val h = list.head
    if (h == e) {
      permutation(list, KCons(e, list delete e)) because
        permutation_refl(list)
    } else {
      permutation(list, KCons(e, list delete e)) because
        (list delete e) == KCons(h, list.tail delete e)
    }
  } holds

  @induct
  def delete_contains[K, V] (list: KList[K, V], a: Item[K, V], b: Item[K, V]) = {
    require(list.contains(a) && a != b)
    list.delete(b).contains(a)
  } holds

  @induct
  def delete_content[K, V] (list: KList[K, V], e: Item[K, V]): Boolean = {
    require(list.contains(e))
    list.content == list.delete(e).content ++ Set(e)
  } holds

  @induct
  def delete_concat[K, V] (l1: KList[K, V], l2: KList[K, V], e: Item[K, V]): Boolean = {
    require(l1 contains e)
    (l1).delete(e) ++ l2 == (l1 ++ l2).delete(e)
  } holds

  @induct
  def delete_comm[K, V] (list: KList[K, V], a: Item[K, V], b: Item[K, V]): Boolean = {
    list.delete(a).delete(b) == list.delete(b).delete(a)
  } holds

  /* Apply this to prove permutation(l1, l3) by transitivity. */
  def permutation_by_tran[K, V] (l1: KList[K, V], l2: KList[K, V], l3: KList[K, V]): Boolean = {
    permutation(l1, l2) && permutation(l2, l3) && permutation_tran(l1, l2, l3)
  } ensuring {
    res => !res || permutation(l1, l3)
  }

  def cons_merge_assoc[K, V] (e: Item[K, V], list1: KList[K, V], list2: KList[K, V]): Boolean = {
    e :: (list1 ++ list2) == (e :: list1) ++ list2
  } holds /* proven by Leon */

  def cons_delete_perm[K, V] (list: KList[K, V], e: Item[K, V]): Boolean = {
    require(list.contains(e))
    permutation(e :: list.delete(e), list) because {
      permutation_refl(list.delete(e)) &&
        permutation_cons_delete(list, e, list.delete(e))
    }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm1[K, V] (h: Item[K, V], t: KList[K, V], pos: KList[K, V], neg: KList[K, V]): Boolean = {
    require(permutation(pos.delete(h) ++ neg, t) && pos.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (pos.delete(h) ++ neg), h :: t) because {
        /* for permutation(pos ++ neg, h::(pos.delete(h))) */
        cons_merge_assoc(h, pos.delete(h), neg) &&
          permutation(pos ++ neg, (h :: pos.delete(h)) ++ neg) because {
          permutation(pos, h :: pos.delete(h)) because {
            cons_delete_perm(pos, h) && permutation_comm(h :: pos.delete(h), pos)
          } && permutation_concat(pos, h :: pos.delete(h), neg)
        } &&
          /* for permutation(h::(pos.delete(h)), h::t) */
          permutation_cons(pos.delete(h) ++ neg, t, h)
      }
    }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm2[K, V] (h: Item[K, V], t: KList[K, V], pos: KList[K, V], neg: KList[K, V]): Boolean = {
    require(permutation(pos ++ neg.delete(h), t) && neg.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (pos ++ neg.delete(h)), h :: t) because {
        /* for permutation(pos ++ neg, h::(pos ++ neg.delete(h))) */
        cons_merge_assoc(h, pos, neg.delete(h)) &&
          permutation(pos ++ neg, (h :: pos) ++ neg.delete(h)) because {
          permutation_by_tran(pos ++ neg, pos ++ (h :: neg.delete(h)), (h :: pos) ++ neg.delete(h)) because {
            /* for permutation(pos ++ neg, pos ++ (h::neg.delete(h))) */
            permutation_by_tran(pos ++ neg, neg ++ pos, pos ++ (h :: neg.delete(h))) because {
              /* for permutation(pos ++ neg, neg ++ pos) */
              permutation_concat_comm(pos, neg) &&
                /* for permutation(neg ++ pos, pos ++ (h::neg.delete(h))) */
                permutation_by_tran(neg ++ pos, (h :: neg.delete(h)) ++ pos, pos ++ (h :: neg.delete(h))) because {
                cons_delete_perm(neg, h) && permutation_comm(h :: neg.delete(h), neg) &&
                  permutation_concat(neg, h :: neg.delete(h), pos) &&
                  permutation_concat_comm(h :: neg.delete(h), pos)
              }
            } &&
              /* for permutation(pos ++ (h::neg.delete(h)), (h::pos) ++ neg.delete(h)) */
              permutation_cons_tail(pos, neg.delete(h), h)
          }
        } &&
          /* for permutation(h::(pos ++ neg.delete(h)), h::t) */
          permutation_cons(pos ++ neg.delete(h), t, h)
      }
    }
  } holds /* proven by Leon */

  def filter_union_perm[K, V] (list: KList[K, V], p: Item[K, V] => Boolean): Boolean = {
    permutation(list.filter(p) ++ list.filterNot(p), list) because {
      list match {
        case KNil()              => trivial
        case KCons(h, t) if p(h) => filter_union_perm(t, p) && filter_union_perm1(h, t, list.filter(p), list.filterNot(p))
        case KCons(h, t)         => filter_union_perm(t, p) && filter_union_perm2(h, t, list.filter(p), list.filterNot(p))
      }
    }
  } holds /* proven by Leon */

  def filter_union_size[K, V] (list: KList[K, V], p: Item[K, V] => Boolean): Boolean = {
    (list.filter(p) ++ list.filterNot(p)).size == list.size because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  def filter_union_content[K, V] (list: KList[K, V], p: Item[K, V] => Boolean): Boolean = {
    (list.filter(p) ++ list.filterNot(p)).content == list.content because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  @induct
  def forall_p_not_in[K, V] (list: KList[K, V], p: Item[K, V] => Boolean, e: Item[K, V]): Boolean = {
    require(list.forall(p) && !p(e))
    !list.contains(e)
  } holds /* proven by Leon */

  @induct
  def filter_sound[K, V] (list: KList[K, V], p: Item[K, V] => Boolean, e: Item[K, V]): Boolean = {
    require(list.filter(p).contains(e))
    list.contains(e) && p(e)
  } holds /* proven by Leon */

  @induct
  def filter_complete[K, V] (list: KList[K, V], p: Item[K, V] => Boolean, e: Item[K, V]): Boolean = {
    require(list.contains(e) && p(e))
    list.filter(p).contains(e)
  } holds /* proven by Leon */

  def disjoint_by_pred[K, V] (pos: KList[K, V], neg: KList[K, V], p: Item[K, V] => Boolean): Boolean = {
    require(pos.forall(p) && neg.forall(!p(_)))
    (pos & neg) == KNil[K, V]() because {
      pos match {
        case KNil()      => trivial
        case KCons(h, t) => check {
          !neg.contains(h) because forall_p_not_in(neg, (x: Item[K, V]) => !p(x), h)
        } && disjoint_by_pred(t, neg, p)
      }
    }
  } holds /* proven by Leon */

  def filter_disjoint[K, V] (list: KList[K, V], p: Item[K, V] => Boolean): Boolean = {
    (list.filter(p) & list.filterNot(p)) == KNil[K, V]() because
      disjoint_by_pred(list.filter(p), list.filterNot(p), p)
  } holds /* proven by Leon */

  def permutation_filter_contains[K, V] (list1: KList[K, V], list2: KList[K, V], p: Item[K, V] => Boolean, x: Item[K, V]): Boolean = {
    require(permutation(list1, list2) && list1.filter(p).contains(x))
    list2.filter(p).contains(x) because {
      filter_sound(list1, p, x) && permutation_contains_lemma(list1, list2, x) && filter_complete(list2, p, x)
    }
  } holds /* proven by Leon */

}
