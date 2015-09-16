package duck.collection

import leon.annotation._
import leon.lang._
import scala.language.postfixOps
import MapOps._

/**
 * Map
 * A key-value map. Each key corresponds to at most one value in the map.
 * Upon each insertion, the value with the same key, if any, is overwritten
 * by the new value.
 * TODO: Prove MapSpec.
 */
@ignore
object MapSpec {
  def insert_commu_lemma[V] (map: KList[V], p1: Item[V], p2: Item[V]): Boolean = {
    require(p1.key != p2.key)
    update(update(map, p1), p2).equals(update(update(map, p2), p1))
  } holds

  def merge_commu_lemma[V] (map1: KList[V], map2: KList[V]): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]())
    (map2 ++ map1).equals(map1 ++ map2)
  } holds

  def merge_assoc_lemma[V] (map1: KList[V], map2: KList[V], map3: KList[V]): Boolean = {
    require((map1.keys & map2.keys) == Nil[BigInt]() &&
      (map2.keys & map3.keys) == Nil[BigInt]() &&
      (map3.keys & map1.keys) == Nil[BigInt]())
    (map1 ++ (map2 ++ map3)).equals((map1 ++ map2) ++ map3)
  } holds
}

object MapOps {

  // brute force
  def subsetOf[V] (map1: KList[V], map2: KList[V]): Boolean = {
    map1 match {
      case Nil()               => true
      case Cons(Item(k, v), t) => val vv = get(map2, k)
        vv.isDefined && vv.get == v && subsetOf(t, map2)
    }
  }

  // use set theory of solver
  def subsetOf_v2[V] (map1: KList[V], map2: KList[V]): Boolean =
    map1.content.subsetOf(map2.content)

  @induct
  def merge[V] (map1: KList[V], map2: KList[V]): KList[V] = {
    map1 match {
      case Nil()      => map2
      case Cons(h, t) => merge(t, update(map2, h))
    }
  } ensuring {
    //res => res.size == map1.size + map2.size - (map1.keys & map2.keys).size
    res => res.size <= map1.size + map2.size
  }

  def update[V] (map: KList[V], data: Item[V]): KList[V] = {
    map match {
      case Nil()               => data :: Nil[V]()
      case Cons(Item(k, v), t) =>
        if (k == data.key) Item(k, data.value) :: t
        else Item(k, v) :: update(map.tail, data)
    }
  }

  def hasKey[V] (map: KList[V], key: BigInt): Boolean = {
    map match {
      case Nil()               => false
      case Cons(Item(k, v), t) => k == key || hasKey(map.tail, key)
    }
  }

  def get[V] (map: KList[V], key: BigInt): Option[V] = {
    map match {
      case Nil()               => None[V]()
      case Cons(Item(k, v), t) => if (k == key) Some[V](v) else get(t, key)
    }
  }
}

object KListLemmas {

}