import leon.annotation.{library, ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import leon.lang.xlang._
import scala.language.postfixOps
import PMap._

/**
 * PMap prototype
 * A prototype of a key-value map. Each key corresponds to at most one value in the map.
 * Upon each insertion, the value with the same key, if any, is overwritten
 * by the new value.
 */
object PMapSpec {
  def insert_commu_lemma[K, V] (map: PMap[K, V], p1: (K, V), p2: (K, V)): Boolean = {
    require(map.isValid() && p1._1 != p2._1)
    (map + p1 + p2).equals(map + p2 + p1)
  } holds

  def merge_commu_lemma[K, V] (map1: PMap[K, V], map2: PMap[K, V]): Boolean = {
    //require((map1 ++ map2).isValid())
    (map2 ++ map1).equals(map1 ++ map2)
  } holds

  def merge_assoc_lemma[K, V] (map1: List[(K, V)], map2: List[(K, V)], map3: List[(K, V)]): Boolean = {
    map1 ++ (map2 ++ map3) == (map1 ++ map2) ++ map3
  } holds
}

@library
object PMap {
  def empty[K, V] = List[(K, V)]()

  def apply[K, V] () = new PMap[K, V](empty[K, V])
}

@library
case class PMap[K, V] (theMap: List[(K, V)]) {

  def ++ (other: PMap[K, V]): PMap[K, V] = merge(other)

  def + (kv: (K, V)): PMap[K, V] = update(kv._1, kv._2)

  def + (k: K, v: V): PMap[K, V] = update(k, v)

  def contains (key: K): Boolean = _contains(key, theMap)

  def get (key: K): Option[V] = _get(key, theMap)

  def update (key: K, value: V): PMap[K, V] = {
    require(this.isValid())
    new PMap(_update(key, value, theMap))
  } ensuring (_.isValid())

  def mergeUnsafe (other: PMap[K, V]) = {
    require(this.isValid())
    new PMap(theMap ++ other.theMap)
  } ensuring (_.isValid()) // counterexample found

  def merge (other: PMap[K, V]) = {
    require(_isValid(this.theMap ++ other.theMap))
    new PMap(_merge(theMap, other.theMap))
  } ensuring { res =>
    res.isValid() && res.theMap.size == other.theMap.size + this.theMap.size
  }

  def content = theMap.content

  def equals (other: PMap[K, V]): Boolean = {
    theMap.size == other.theMap.size && _subsetOf(theMap, other.theMap)
  }

  def isValid () = _isValid(theMap)


  private def _isValid (map: List[(K, V)]): Boolean = {
    map.size <= 1 || (!_contains(map.head._1, map.tail) && _isValid(map.tail))
  }
  private def _subsetOf (map1: List[(K, V)], map2: List[(K, V)]): Boolean = {
    map1 match {
      case Nil()           => true
      case Cons((k, v), t) => {
        val vv = _get(k, map2)
        vv.isDefined && vv.get == v && _subsetOf(t, map2)
      }
    }
  }

  @induct
  private def _merge (map1: List[(K, V)], map2: List[(K, V)]): List[(K, V)] = {
    require(_isValid(map1 ++ map2))
    map1 match {
      case Nil()           => map2
      case Cons((k, v), t) => _merge(t, _update(k, v, map2))
    }
  } ensuring {
    res => _isValid(res) //&& res.size == map1.size + map2.size
  }

  private def _update (key: K, value: V, map: List[(K, V)]): List[(K, V)] = {
    map match {
      case Nil()           => List((key, value))
      case Cons((k, v), t) => {
        if (k == key) (k, value) :: t
        else (k, v) :: _update(key, value, map.tail)
      }
    }
  }

  private def _contains (key: K, map: List[(K, V)]): Boolean = {
    map match {
      case Nil()           => false
      case Cons((k, v), t) => k == key || _contains(key, theMap.tail)
    }
  }

  private def _get (key: K, map: List[(K, V)]): Option[V] = {
    map match {
      case Nil()           => None[V]()
      case Cons((k, v), t) => if (k == key) Some[V](v) else _get(key, t)
    }
  }
}

object PMapLemmas {
  @induct
  def merge_lemma[K, V] (map1: PMap[K, V], map2: PMap[K, V]): Boolean = {
    require(map1.isValid() && map2.isValid())
    (map1 ++ map2).isValid()
  } holds

}