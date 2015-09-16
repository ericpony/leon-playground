package duck.collection

import leon.annotation._
import leon.lang._
import leon.proof._
import scala.language.postfixOps
import FIFOMapLemmas._

/**
 * Map
 * A key-value map. Each key corresponds to at most one value in the map.
 * Upon each insertion, the value with the same key, if any, is overwritten
 * by the new value.
 *
 * TODO: prove MapSpec
 */
@ignore
object MapSpec {
  def insert_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V]): Boolean = {
    require(p1.key != p2.key)
    map.update(p1).update(p2).equals(map.update(p2).update(p1))
    //map.update(p1).update(p2).content == map.update(p2).update(p1).content
  } holds /* timeout */

  def merge_commu_lemma[V] (map1: KList[V], map2: KList[V]): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]())
    (map2 ++ map1).equals(map1 ++ map2)
  } holds /* timeout */

  def merge_assoc_lemma[V] (map1: KList[V], map2: KList[V], map3: KList[V]): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]() &&
      (map2.keys & map3.keys) == Nil[BigInt]() &&
      (map3.keys & map1.keys) == Nil[BigInt]())
    (map1 ++ (map2 ++ map3)).equals((map1 ++ map2) ++ map3)
  } holds /* timeout */
}

/**
 * FIFO Map
 * A key-value-queue map. Each key corresponds to a queue of values.
 * Upon each insertion, the value is append to the queue associated with the given key.
 *
 * TODO: prove merge_commu_lemma
 */
object FIFOMapSpec {

  @induct
  def insert_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V], key: BigInt): Boolean = {
    require(p1.key != p2.key)
    (p2 :: p1 :: map).getAll(key) == (p1 :: p2 :: map).getAll(key)
  } holds /* verified by Leon */

  @induct
  def merge_commu_lemma[V] (map1: KList[V], map2: KList[V], key: BigInt): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]())
    (map2 ++ map1).getAll(key) == (map1 ++ map2).getAll(key)
  } holds /* timeout */

  @induct
  def merge_assoc_lemma[V] (map1: KList[V], map2: KList[V], map3: KList[V], key: BigInt): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]() &&
      (map2.keys & map3.keys) == Nil[BigInt]() &&
      (map3.keys & map1.keys) == Nil[BigInt]())
    (map1 ++ (map2 ++ map3)).getAll(key) == ((map1 ++ map2) ++ map3).getAll(key)
  } holds /* verified by Leon */
}

object FIFOMapLemmas {
  @induct
  def get_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V], key: BigInt): Boolean = {
    require(p1.key != p2.key)
    (p2 :: p1 :: map).getFirst(key) == (p1 :: p2 :: map).getFirst(key)
  } holds /* verified by Leon */
}