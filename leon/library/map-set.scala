package duck.collection

import duck.suger._
import duck.proof.KListLemmas._
import scala.language.postfixOps
import leon.annotation._
import leon.lang._
import leon.proof._
import SetMapLemmas._
import SetMapOps._

/**
 * Set Map
 * A key-value-set map. Each key corresponds to a set of values.
 * Upon each insertion, the value is add to the set associated with the given key.
 *
 * TODO: prove getAll_perm_lemma
 */
@ignore
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

  @library
  def delete[V] (list: KList[V], e: Item[V]): KList[V] = {
    if (list == Nil[V]()) list
    else if (list.head == e) list.tail
    else Cons(list.head, delete(list.tail, e))
  } ensuring { res =>
    res.size == (if (list contains e) list.size - 1 else list.size) &&
      res.content.subsetOf(list.content)
  } /* verified by Leon */

  @library
  def permutation[V] (l1: KList[V], l2: KList[V]): Boolean = {
    if (l1 == Nil[V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res => res implies
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
        get_perm_contain_lemma(l1, l2, key)
  } holds /* verified by Leon */

  def get_perm_contain_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    val l1 = map1.getAll(key)
    val l2 = map2.getAll(key)
    if (l1 == Nil[V]())
      permutation(l1, l2) because
        permutation_hasKey_lemma(map1, map2, key)
    else {
      permutation(l1, l2) because {
        val h1 = map1.get(key).get
        val m1 = delete(map1, h1)
        val m2 = delete(map2, h1)
        l1.head == h1 &&
          check { l2.contains(h1) because get_contain_lemma(map2, h1) } &&
          check {
            permutation(m1, m2) because
              permutation_delete(map1, map2, h1)
          } &&
          check {
            permutation(m1.getAll(key), m2.getAll(key)) because
              get_perm_contain_lemma(m1, m2, key)
          } &&
          check { m1.getAll(key) == delete(l1, h1) because get_delete_lemma(map1, h1, key) } &&
          check { m2.getAll(key) == delete(l2, h1) because get_delete_lemma(map2, h1, key) } &&
          check { permutation(delete(l2, h1), l1.tail) } &&
          check { permutation_cons_delete(l2, h1, l1.tail) } &&
          check { permutation(l1, l2) }
      }
    }
  } holds

  def permutation_hasKey_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) iff map2.hasKey(key) because {
      permutation_hasKey_lemma2(map1, map2, key) &&
        permutation_hasKey_lemma2(map2, map1, key)
    }
  } holds

  @induct
  def permutation_hasKey_lemma2[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require(permutation(map1, map2))
    map1.hasKey(key) implies map2.hasKey(key) because {
      !map1.hasKey(key) || map2.contains(map1.get(key).get)
    }
  } holds

//    @induct
//    def permutation_get_tail_lemma[V] (map1: KList[V], map2: KList[V], e: Item[V]): Boolean = {
//      require(permutation(map1, map2))
//      map1.hasKey(key) implies map2.hasKey(key) because {
//        map1.hasKey(key) implies map2.contains(map1.get(key).get)
//      }
//    } holds

  @induct
  def get_delete_lemma[V] (map: KList[V], e: Item[V], key: BigInt): Boolean = {
    require(map contains e)
    delete(map, e).getAll(key) == delete(map.getAll(key), e)
  } holds

  @induct
  def get_contain_lemma[V] (map: KList[V], e: Item[V]): Boolean = {
    require(map contains e)
    map.getAll(e.key) contains e
  } holds
}
