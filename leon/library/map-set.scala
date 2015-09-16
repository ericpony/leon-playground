package duck.collection

import leon.annotation._
import leon.lang._
import leon.proof._
import scala.language.postfixOps

/**
 * Set Map
 * A key-value-set map. Each key corresponds to a set of values.
 * Upon each insertion, the value is add to the set associated with the given key.
 *
 * TODO: prove merge_commu_lemma
 */
object SetMapSpec {
  @induct
  def insert_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V], key: BigInt): Boolean = {
    (p2 :: p1 :: map).getAll(key).content == (p1 :: p2 :: map).getAll(key).content
  } holds /* verified by Leon */

  @induct
  def merge_commu_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    (map2 ++ map1).getAll(key).content == (map1 ++ map2).getAll(key).content
  } holds /* timeout */

  @induct
  def merge_assoc_lemma[V] (map1: KList[V], map2: KList[V], map3: KList[V], key: BigInt): Boolean = {
    (map1 ++ (map2 ++ map3)).getAll(key).content == ((map1 ++ map2) ++ map3).getAll(key).content
  } holds /* verified by Leon */
}

object SetMapLemmas {}