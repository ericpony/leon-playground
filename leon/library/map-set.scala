package duck.collection

import duck.proof.KListLemmas._
import duck.collection.KListOps._
import leon.annotation._
import leon.lang._
import leon.proof._
import SetMapLemmas._
import SetMapOps._
import scala.language.postfixOps

/**
 * Set Map
 * A key-value-set map. Each key corresponds to a set of values.
 * Upon each insertion, the value is add to the set associated with the given key.
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
  def merge_perm_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    val l1 = map1 ++ map2
    val l2 = map2 ++ map1
    permutation(l1.getAll(key), l2.getAll(key)) because
      permutation_concat_comm(map1, map2) &&
        permutation_getAll_lemma(l1, l2, key)
  } holds /* verified by Leon */
}