package duck.spec

import duck.collection.KList._
import duck.collection.List._
import duck.collection._
import duck.proof.DistinctOps._

//import leon.collection._
import leon.lang._
import leon.annotation._

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
    val m1 = map2 ++ map1
    val m2 = map1 ++ map2
    m1.size == m2.size && m1.content == m2.content
  } holds /* verified by Leon */

  def merge_commu_lemma2[K, V] (map1: KList[K, V], map2: KList[K, V]) = {
    require((map1.keys & map2.keys) == Nil[K]() && distinct(map1.keys) && distinct(map2.keys))
    val m1 = merge(map1, map2)
    val m2 = merge(map2, map1)
    m1.size == m2.size && m1.content == m2.content
  } holds /* timeout */

  def merge_assoc_lemma[K, V] (map1: KList[K, V], map2: KList[K, V], map3: KList[K, V]) = {
    require((map1.keys & map2.keys) == Nil[K]() &&
      (map2.keys & map3.keys) == Nil[K]() &&
      (map3.keys & map1.keys) == Nil[K]())
    (map1 ++ (map2 ++ map3)).content == ((map1 ++ map2) ++ map3).content
  } holds /* verified by Leon */

  @induct
  def merge[K, V] (map1: KList[K, V], map2: KList[K, V]): KList[K, V] = {
    map1 match {
      case KNil() => map2
      case KCons(hd, tl) => merge(tl, map2.update(hd))
    }
  }
//  ensuring {
//    res => (distinct(map1.keys) &&
//      distinct(map2.keys) &&
//      (map1.keys & map2.keys) == Nil[K]()) ==> (res.size == map1.size + map2.size)
//  }

}

object PairMapLemmas {}
