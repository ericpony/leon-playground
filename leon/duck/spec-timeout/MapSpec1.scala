import leon.annotation._
import leon.collection._
import leon.lang._
import scala.language.postfixOps

/**
 * SMap prototype
 * A prototype of a key-value-set map. Each key corresponds to a set of values.
 * Upon each insertion, the new value is added to the set of the value with the same key.
 */
object SMapSpec {
  def insert_commu_lemma[K, V] (map: SMap[K, V], p1: (K, V), p2: (K, V)): Boolean = {
    require(map.isValid())
    (map + p1 + p2).equals(map + p2 + p1)
  } holds

  def merge_commu_lemma[K, V] (map1: SMap[K, V], map2: SMap[K, V]): Boolean = {
    require(map1.isValid() && map2.isValid())
    (map2 ++ map1).equals(map1 ++ map2)
  } holds

  def merge_assoc_lemma[K, V] (map1: List[(K, V)], map2: List[(K, V)], map3: List[(K, V)]): Boolean = {
    map1 ++ (map2 ++ map3) == (map1 ++ map2) ++ map3
  } holds
}

@library
object SMap {
  def empty[K, V] = List[(K, Set[V])]()

  def apply[K, V] () = new SMap[K, V](empty[K, V])
}

@library
case class SMap[K, V] (theMap: List[(K, Set[V])]) {

  def ++ (other: SMap[K, V]): SMap[K, V] = merge(other)

  def + (kv: (K, V)): SMap[K, V] = update(kv._1, kv._2)

  def + (k: K, v: V): SMap[K, V] = update(k, v)

  def contains (key: K): Boolean = _contains(key, theMap)

  def contains2 (key: K): Boolean = !get(key).isEmpty

  def get (key: K): Set[V] = _get(key, theMap)

  def update (key: K, value: V): SMap[K, V] = {
    require(this.isValid())
    new SMap(_update(key, Set(value), theMap))
  } ensuring (_.isValid())

  def merge (other: SMap[K, V]) = {
    require(this.isValid())
    new SMap(_merge(theMap, other.theMap))
  } ensuring (_.isValid())

  def content = theMap.content

  def equals (other: SMap[K, V]): Boolean = {
    theMap.size == other.theMap.size && _subsetOf(theMap, other.theMap)
  }

  def isValid () = _isValid(theMap)

  private def _isValid (map: List[(K, Set[V])]): Boolean = {
    map.size <= 1 || (!_contains(map.head._1, map.tail) && _isValid(map.tail))
  }

  private def _subsetOf (map1: List[(K, Set[V])], map2: List[(K, Set[V])]): Boolean = {
    map1 match {
      case Nil()           => true
      case Cons((k, v), t) => _get(k, map2) == v && _subsetOf(t, map2)
    }
  }

  private def _merge (map1: List[(K, Set[V])], map2: List[(K, Set[V])]): List[(K, Set[V])] = {
    map1 match {
      case Nil()           => map2
      case Cons((k, v), t) => _merge(_update(k, v, map2), t)
    }
  }

  private def _update (key: K, values: Set[V], map: List[(K, Set[V])]): List[(K, Set[V])] = {
    map match {
      case Nil()           => List((key, values))
      case Cons((k, v), t) =>
        if (k == key) (k, v ++ values) :: t
        else (k, v) :: _update(key, values, map.tail)
    }
  }

  private def _contains (key: K, map: List[(K, Set[V])]): Boolean = {
    map match {
      case Nil()           => false
      case Cons((k, v), t) => k == key || _contains(key, theMap.tail)
    }
  }

  private def _get (key: K, map: List[(K, Set[V])]): Set[V] = {
    map match {
      case Nil()           => Set[V]()
      case Cons((k, v), t) => if (k == key) v else _get(key, t)
    }
  }
}