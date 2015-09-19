package duck.proof

import duck.suger._
import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._
import KListOps._

import scala.language.postfixOps

@library
object KListLemmas {

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

  def permutation_hasKey_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) iff map2.hasKey(key) because {
      permutation_hasKey_lemma2(map1, map2, key) &&
        permutation_hasKey_lemma2(map2, map1, key)
    }
  } holds /* verified by Leon */

  /* This lemma is only used in permutation_hasKey_lemma */
  @induct
  def permutation_hasKey_lemma2[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) implies map2.hasKey(key) because {
      !map1.hasKey(key) || map2.contains(map1.get(key).get)
    }
  } holds /* verified by Leon */

  /**
   * WARNING: Leon may take 2~30 seconds to verify this lemma.
   **/
  def permutation_getAll_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    val l1 = map1.getAll(key)
    val l2 = map2.getAll(key)

    permutation(l1, l2) because {
      if (l1 == Nil[V]())
        permutation(l1, l2) because
          l1 == Nil[V]() iff !l1.hasKey(key) &&
          l2 == Nil[V]() iff !l2.hasKey(key) &&
          permutation_hasKey_lemma(map1, map2, key)
      else {
        val h1 = map1.get(key).get
        val m1 = delete(map1, h1)
        val m2 = delete(map2, h1)
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
          check { m2.getAll(key) == delete(l2, h1) because getAll_delete_lemma(map2, h1, key) } &&
          permutation(delete(l2, h1), l1.tail) &&
          permutation_cons_delete(l2, h1, l1.tail)
      }
    }
  } holds /* verified by Leon */

  @induct
  def getAll_delete_lemma[V] (map: KList[V], e: Item[V], key: BigInt): Boolean = {
    require(map.contains(e) && e.key == key)
    delete(map, e).getAll(key) == delete(map.getAll(key), e)
  } holds /* verified by Leon */

  @induct
  def getAll_contain_lemma[V] (map: KList[V], e: Item[V]): Boolean = {
    require(map contains e)
    map.getAll(e.key) contains e
  } holds /* verified by Leon */

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

  /* Apply this to prove permutation(l1, l3) by transitivity. */
  def permutation_by_tran[V] (l1: KList[V], l2: KList[V], l3: KList[V]): Boolean = {
    permutation(l1, l2) && permutation(l2, l3) && permutation_tran(l1, l2, l3)
  } ensuring {
    res => !res || permutation(l1, l3)
  }

  def cons_merge_assoc[V] (e: Item[V], list1: KList[V], list2: KList[V]): Boolean = {
    e :: (list1 ++ list2) == (e :: list1) ++ list2
  } holds /* proven by Leon */

  def cons_delete_perm[V] (list: KList[V], e: Item[V]): Boolean = {
    require(list.contains(e))
    permutation(e :: delete(list, e), list) because { permutation_refl(delete(list, e)) && permutation_cons_delete(list, e, delete(list, e)) }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm1[V] (h: Item[V], t: KList[V], pos: KList[V], neg: KList[V]): Boolean = {
    require(permutation(delete(pos, h) ++ neg, t) && pos.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (delete(pos, h) ++ neg), h :: t) because {
        /* for permutation(pos ++ neg, h::(delete(pos, h))) */
        cons_merge_assoc(h, delete(pos, h), neg) && permutation(pos ++ neg, (h :: delete(pos, h)) ++ neg) because {
          permutation(pos, h :: delete(pos, h)) because {
            cons_delete_perm(pos, h) && permutation_comm(h :: delete(pos, h), pos)
          } && permutation_concat(pos, h :: delete(pos, h), neg)
        } &&
          /* for permutation(h::(delete(pos, h)), h::t) */
          permutation_cons(delete(pos, h) ++ neg, t, h)
      }
    }
  } holds /* proven by Leon */

  /* This lemma is applied in filter_union_perm. */
  def filter_union_perm2[V] (h: Item[V], t: KList[V], pos: KList[V], neg: KList[V]): Boolean = {
    require(permutation(pos ++ delete(neg, h), t) && neg.contains(h))
    permutation(pos ++ neg, h :: t) because {
      permutation_by_tran(pos ++ neg, h :: (pos ++ delete(neg, h)), h :: t) because {
        /* for permutation(pos ++ neg, h::(pos ++ delete(neg, h))) */
        cons_merge_assoc(h, pos, delete(neg, h)) && permutation(pos ++ neg, (h :: pos) ++ delete(neg, h)) because {
          permutation_by_tran(pos ++ neg, pos ++ (h :: delete(neg, h)), (h :: pos) ++ delete(neg, h)) because {
            /* for permutation(pos ++ neg, pos ++ (h::delete(neg, h))) */
            permutation_by_tran(pos ++ neg, neg ++ pos, pos ++ (h :: delete(neg, h))) because {
              /* for permutation(pos ++ neg, neg ++ pos) */
              permutation_concat_comm(pos, neg) &&
                /* for permutation(neg ++ pos, pos ++ (h::delete(neg, h))) */
                permutation_by_tran(neg ++ pos, (h :: delete(neg, h)) ++ pos, pos ++ (h :: delete(neg, h))) because {
                cons_delete_perm(neg, h) && permutation_comm(h :: delete(neg, h), neg) && permutation_concat(neg, h :: delete(neg, h), pos) &&
                  permutation_concat_comm(h :: delete(neg, h), pos)
              }
            } &&
              /* for permutation(pos ++ (h::delete(neg, h)), (h::pos) ++ delete(neg, h)) */
              permutation_cons_tail(pos, delete(neg, h), h)
          }
        } &&
          /* for permutation(h::(pos ++ delete(neg, h)), h::t) */
          permutation_cons(pos ++ delete(neg, h), t, h)
      }
    }
  } holds /* proven by Leon */

  def filter_union_perm[V] (list: KList[V], p: Item[V] => Boolean): Boolean = {
    permutation(list.filter(p) ++ list.filterNot(p), list) because {
      list match {
        case Nil()              => trivial
        case Cons(h, t) if p(h) => filter_union_perm(t, p) && filter_union_perm1(h, t, list.filter(p), list.filterNot(p))
        case Cons(h, t)         => filter_union_perm(t, p) && filter_union_perm2(h, t, list.filter(p), list.filterNot(p))
      }
    }
  } holds /* proven by Leon */

  def filter_union_size[V] (list: KList[V], p: Item[V] => Boolean): Boolean = {
    (list.filter(p) ++ list.filterNot(p)).size == list.size because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  def filter_union_content[V] (list: KList[V], p: Item[V] => Boolean): Boolean = {
    (list.filter(p) ++ list.filterNot(p)).content == list.content because {
      filter_union_perm(list, p)
    }
  } holds /* proven by Leon */

  @induct
  def forall_p_not_in[V] (list: KList[V], p: Item[V] => Boolean, e: Item[V]): Boolean = {
    require(list.forall(p) && !p(e))
    !list.contains(e)
  } holds /* proven by Leon */

  @induct
  def filter_in[V] (list: KList[V], p: Item[V] => Boolean, e: Item[V]): Boolean = {
    require(list.contains(e) && p(e))
    list.filter(p).contains(e)
  } holds /* proven by Leon */

  def disjoint_by_pred[V] (pos: KList[V], neg: KList[V], p: Item[V] => Boolean): Boolean = {
    require(pos.forall(p) && neg.forall(!p(_)))
    (pos & neg) == Nil[V]() because {
      pos match {
        case Nil()      => trivial
        case Cons(h, t) => check {
          !neg.contains(h) because forall_p_not_in(neg, (x: Item[V]) => !p(x), h)
        } && disjoint_by_pred(t, neg, p)
      }
    }
  } holds /* proven by Leon */

  def filter_disjoint[V] (list: KList[V], p: Item[V] => Boolean): Boolean = {
    (list.filter(p) & list.filterNot(p)) == Nil[V]() because
      disjoint_by_pred(list.filter(p), list.filterNot(p), p)
  } holds /* proven by Leon */

}
