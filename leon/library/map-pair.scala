import duck.collection.KList._
import leon.lang._
import leon.annotation._
import leon.collection._
import scala.language.postfixOps

/**
 * Pair Map
 * A key-value-pair map. Each key corresponds to at most one value in the map.
 * Upon each insertion, the value with the same key, if any, is overwritten
 * by the new value.
 */
object PairMapSpec {
  @induct
  def insert_commu_lemma[K, V] (map: KList[K, V], p1: Item[K, V], p2: Item[K, V]) = {
    require(p1.key != p2.key)
    map.update(p1).update(p2).content == map.update(p2).update(p1).content
  } holds /* verified by Leon */

  def merge_commu_lemma[K, V] (map1: KList[K, V], map2: KList[K, V]) = {
    require((map1.keys & map2.keys) == Nil[K]())
    (map2 ++ map1).content == (map1 ++ map2).content
  } holds /* verified by Leon */

  def merge_assoc_lemma[K, V] (map1: KList[K, V], map2: KList[K, V], map3: KList[K, V]) = {
    require((map1.keys & map2.keys) == Nil[K]() &&
      (map2.keys & map3.keys) == Nil[K]() &&
      (map3.keys & map1.keys) == Nil[K]())
    (map1 ++ (map2 ++ map3)).content == ((map1 ++ map2) ++ map3).content
  } holds /* verified by Leon */
}

object PairMapLemmas {}
