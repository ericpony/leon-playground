package duck.collection

import duck.sugar._
import duck.proof.KListLemmas._
import leon.proof._
import leon.lang._
import leon.annotation._
import leon.collection._

case class Item[V] (key: BigInt, value: V)

case class KCons[V] (h: Item[V], t: KList[V]) extends KList[V]

case class KNil[V] () extends KList[V]

/**
 * KList
 * List of key-value pairs with integer keys
 */
@library
sealed abstract class KList[V] {

  def size: BigInt = (this match {
    case KNil()      => BigInt(0)
    case KCons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def content: Set[Item[V]] = this match {
    case KNil()      => Set[Item[V]]()
    case KCons(h, t) => Set(h) ++ t.content
  }

  def contains (v: Item[V]): Boolean = (this match {
    case KCons(h, t) if h == v => true
    case KCons(_, t)           => t.contains(v)
    case KNil()                => false
  }) ensuring {
    _ == (content contains v) && hasKey(v.key)
  }

  def ++ (that: KList[V]): KList[V] = (this match {
    case KNil()       => that
    case KCons(x, xs) => KCons[V](x, xs ++ that)
  }) ensuring { res =>
    (res.content == this.content ++ that.content) &&
      (res.size == this.size + that.size) &&
      (that != KNil[V]() || res == this)
  }

  def head: Item[V] = {
    require(this != KNil[V]())
    val KCons(h, _) = this
    h
  }

  def tail: KList[V] = {
    require(this != KNil[V]())
    val KCons(_, t) = this
    t
  }

  def :: (t: Item[V]): KList[V] = KCons(t, this)

  def :+ (t: Item[V]): KList[V] = {
    this match {
      case KNil()       => KCons(t, this)
      case KCons(x, xs) => KCons(x, xs :+ (t))
    }
  } ensuring (res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: KList[V] = {
    this match {
      case KNil()       => this
      case KCons(x, xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def keys: List[BigInt] = mapList(item => item.key)

  def values: List[V] = mapList(item => item.value)

  def take (i: BigInt): KList[V] = {
    (this, i) match {
      case (KNil(), _)      => KNil[V]()
      case (KCons(h, t), i) => if (i <= BigInt(0)) KNil[V]() else KCons(h, t.take(i - 1))
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if (i <= 0) BigInt(0)
      else if (i >= this.size) this.size
      else i
      ))
  }

  def drop (i: BigInt): KList[V] = {
    (this, i) match {
      case (KNil(), _)      => KNil[V]()
      case (KCons(h, t), i) => if (i <= BigInt(0)) KCons[V](h, t) else t.drop(i - 1)
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if (i <= 0) this.size
      else if (i >= this.size) BigInt(0)
      else this.size - i
      ))
  }

  def slice (from: BigInt, to: BigInt): KList[V] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to - from)
  }

  def replace (from: Item[V], to: Item[V]): KList[V] = {
    this match {
      case KNil()      => KNil[V]()
      case KCons(h, t) =>
        val r = t.replace(from, to)
        if (h == from) KCons(to, r) else KCons(h, r)
    }
  } ensuring { (res: KList[V]) =>
    res.size == this.size &&
      res.content == (
        (this.content -- Set(from)) ++
          (if (this.content contains from) Set(to) else Set[Item[V]]())
        )
  }

  /**
   * Delete ALL occurrences of e from the list
   */
  def - (e: Item[V]): KList[V] = {
    this match {
      case KCons(h, t) => if (e == h) t - e else KCons(h, t - e)
      case KNil()      => KNil[V]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == this.content -- Set(e)
  }

  def -- (that: KList[V]): KList[V] = {
    this match {
      case KCons(h, t) => if (that.contains(h)) t -- that else KCons(h, t -- that)
      case KNil()      => KNil[V]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == this.content -- that.content
  }

  def & (that: KList[V]): KList[V] = {
    this match {
      case KCons(h, t) => if (that.contains(h)) KCons(h, t & that) else t & that
      case KNil()      => KNil[V]()
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content == (this.content & that.content)
  }

  // def ~ (that: KList[V]) = KListOps.permutation(this, that)
  def ~ (that: KList[V]) = this.content == that.content

  def update (data: Item[V]): KList[V] = {
    this match {
      case KNil()               => data :: KNil[V]()
      case KCons(Item(k, v), t) =>
        if (k == data.key) Item(k, data.value) :: t
        else Item(k, v) :: t.update(data)
    }
  }

  def hasKey (key: BigInt): Boolean = {
    this match {
      case KNil()               => false
      case KCons(Item(k, v), t) => k == key || t.hasKey(key)
    }
  } ensuring {
    res => {
      res implies
        get(key).isDefined and
        contains(get(key).get) and
        getAll(key) != KNil[V]()
    } and {
      !res implies
        !get(key).isDefined and
        getAll(key) == KNil[V]()
    }
  }

  /**
   * Get the first element in this list with the provided key.
   */
  def getFirst (key: BigInt): Option[Item[V]] = {
    this match {
      case KNil()      => None[Item[V]]()
      case KCons(h, t) => if (h.key == key) Some[Item[V]](h) else t.getFirst(key)
    }
  } ensuring { res =>
    res.isDefined implies
      res.get.key == key &&
        res.get == getAll(key).head
  }

  /**
   * Get the last element in this list with the provided key.
   */
  def getLast (key: BigInt) = this.reverse.getFirst(key)

  /**
   * Get all elements in this list with the provided key.
   * The order in which the elements are stored in the returned list
   * is consistent with the order they are stored in the original list.
   * Note: This version of getAll is easier to verify for Leon than
   * the concise version
   * def getAll (key: BigInt) = this.filter(item => item.key == key).
   */
  def getAll (key: BigInt): KList[V] = {
    this match {
      case KNil()      => KNil[V]()
      case KCons(h, t) => if (h.key == key) KCons(h, t.getAll(key)) else t.getAll(key)
    }
  } ensuring { res =>
    res.size <= size and
      res.content.subsetOf(content) and
      res.forall(item => item.key == key) and
      (res != KNil[V]() implies hasKey(key))
  }

  /**
   * Get an element from the list with the provided key.
   */
  def get = getFirst _

  /**
   * Obtain a new list by removing the first occurrence of e
   * from this list.
   */
  def deleteFirst (e: Item[V]): KList[V] = {
    if (this == KNil[V]()) this
    else if (head == e) tail
    else KCons(head, tail.deleteFirst(e))
  } ensuring { res =>
    if (contains(e)) {
      res.size == size - 1 &&
        res.content == content -- Set(e) because delete_content(this, e)
    } else {
      res.size == size &&
        res.content == content
    }
  }

  /**
   * Obtain a new list by removing the first element with
   * the provided key from this list.
   */
  def deleteFirst (key: BigInt): KList[V] = {
    this match {
      case KNil()      => this
      case KCons(h, t) => if (h.key == key) t else KCons(h, t.deleteFirst(key))
    }
  } ensuring { res =>
    if (hasKey(key)) {
      val e = getFirst(key).get
      res.size == size - 1 &&
        res.content == content -- Set(e) because delete_content(this, e)
    } else {
      res.size == size &&
        res.content == content
    }
  }

  /**
   * Obtain a new list by removing the last element with
   * the provided key from this list.
   */
  def deleteLast (key: BigInt) = this.reverse.deleteFirst(key)

  /**
   * Obtain a new list by removing all element with the
   * provided key from this list.
   */
  def deleteAll (key: BigInt): KList[V] = {
    this match {
      case KNil()      => this
      case KCons(h, t) => if (h.key == key) t.deleteAll(key) else KCons(h, t.deleteAll(key))
    }
  } ensuring { res =>
    res.size <= this.size and
      res.content.subsetOf(this.content) and
      res.forall(item => item.key != key)
  }

  def deleteAll (e: Item[V]) = this - e

  def delete (key: BigInt) = deleteFirst(key)

  def delete (e: Item[V]) = deleteFirst(e)

  def init: KList[V] = {
    require(!isEmpty)
    ((this: @unchecked) match {
      case KCons(h, KNil()) =>
        KNil[V]()
      case KCons(h, t)      =>
        KCons[V](h, t.init)
    })
  } ensuring { (r: KList[V]) =>
    r.size == this.size - 1 &&
      r.content.subsetOf(this.content)
  }

  def last: Item[V] = {
    require(!isEmpty)
    (this: @unchecked) match {
      case KCons(h, KNil()) => h
      case KCons(_, t)      => t.last
    }
  } ensuring { this.contains _ }

  def lastOption: Option[Item[V]] = {
    this match {
      case KCons(h, t) => t.lastOption.orElse(Some(h))
      case KNil()      => None[Item[V]]()
    }
  } ensuring { _.isDefined != this.isEmpty }

  def headOption: Option[Item[V]] = {
    this match {
      case KCons(h, t) => Some(h)
      case KNil()      => None[Item[V]]()
    }
  } ensuring { _.isDefined != this.isEmpty }

  def unique: KList[V] = this match {
    case KNil()      => KNil()
    case KCons(h, t) => KCons(h, t.unique - h)
  }

  def rotate (s: BigInt): KList[V] = {
    if (isEmpty) KNil[V]()
    else drop(s mod size) ++ take(s mod size)
  } ensuring {
    res => res.size == this.size
  }

  def isEmpty = this match {
    case KNil() => true
    case _      => false
  }

  // Higher-order API
  def map[R] (f: Item[V] => Item[R]): KList[R] = {
    this match {
      case KNil()      => KNil[R]()
      case KCons(h, t) => f(h) :: t.map(f)
    }
  } ensuring { _.size == this.size }

  def mapList[R] (f: Item[V] => R): List[R] = {
    this match {
      case KNil()      => Nil[R]()
      case KCons(h, t) => f(h) :: t.mapList(f)
    }
  } ensuring { _.size == this.size }

  def foldLeft[R] (z: R)(f: (R, Item[V]) => R): R = this match {
    case KNil()      => z
    case KCons(h, t) => t.foldLeft(f(z, h))(f)
  }

  def foldRight[R] (z: R)(f: (Item[V], R) => R): R = this match {
    case KNil()      => z
    case KCons(h, t) => f(h, t.foldRight(z)(f))
  }

  def scanLeft[R] (z: Item[R])(f: (Item[R], Item[V]) => Item[R]): KList[R] = {
    this match {
      case KNil()      => z :: KNil()
      case KCons(h, t) => z :: t.scanLeft(f(z, h))(f)
    }
  } ensuring { !_.isEmpty }

  def scanRight[R] (z: Item[R])(f: (Item[V], Item[R]) => Item[R]): KList[R] = {
    this match {
      case KNil()      => z :: KNil[R]()
      case KCons(h, t) =>
        val rest@KCons(h1, _) = t.scanRight(z)(f)
        f(h, h1) :: rest
    }
  } ensuring { !_.isEmpty }

  def filter (p: Item[V] => Boolean): KList[V] = {
    this match {
      case KNil()              => KNil[V]()
      case KCons(h, t) if p(h) => KCons(h, t.filter(p))
      case KCons(_, t)         => t.filter(p)
    }
  } ensuring { res =>
    res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(p)
  }

  def filterNot (p: Item[V] => Boolean): KList[V] =
    filter(!p(_)) ensuring { res =>
      res.size <= this.size &&
        res.content.subsetOf(this.content) &&
        res.forall(!p(_))
    }

  def partition (p: Item[V] => Boolean): (KList[V], KList[V]) = {
    this match {
      case KNil()      => (KNil[V](), KNil[V]())
      case KCons(h, t) =>
        val (l1, l2) = t.partition(p)
        if (p(h)) (h :: l1, l2)
        else (l1, h :: l2)
    }
  } ensuring { res =>
    res._1 == filter(p) &&
      res._2 == filterNot(p)
  }

  // In case we implement for-comprehensions
  def withFilter (p: Item[V] => Boolean) = filter(p)

  def forall (p: Item[V] => Boolean): Boolean = this match {
    case KNil()      => true
    case KCons(h, t) => p(h) && t.forall(p)
  }

  def exists (p: Item[V] => Boolean) = !forall(!p(_))

  def find (p: Item[V] => Boolean): Option[Item[V]] = {
    this match {
      case KNil()              => None[Item[V]]()
      case KCons(h, t) if p(h) => Some(h)
      case KCons(_, t)         => t.find(p)
    }
  } ensuring { res =>
    res match {
      case Some(r) => (content contains r) && p(r)
      case None()  => true
    }
  }

  def groupBy[R] (f: Item[V] => R): Map[R, KList[V]] = this match {
    case KNil()      => Map.empty[R, KList[V]]
    case KCons(h, t) =>
      val key: R = f(h)
      val rest: Map[R, KList[V]] = t.groupBy(f)
      val prev: KList[V] = if (rest isDefinedAt key) rest(key) else KNil[V]()
      (rest ++ Map((key, h :: prev))): Map[R, KList[V]]
  }

  def takeWhile (p: Item[V] => Boolean): KList[V] = {
    this match {
      case KCons(h, t) if p(h) => KCons(h, t.takeWhile(p))
      case _                   => KNil[V]()
    }
  } ensuring { res =>
    (res forall p) &&
      (res.size <= this.size) &&
      (res.content subsetOf this.content)
  }

  def dropWhile (p: Item[V] => Boolean): KList[V] = {
    this match {
      case KCons(h, t) if p(h) => t.dropWhile(p)
      case _                   => this
    }
  } ensuring { res =>
    (res.size <= this.size) &&
      (res.content subsetOf this.content) &&
      (res.isEmpty || !p(res.head))
  }

  def count (p: Item[V] => Boolean): BigInt = {
    this match {
      case KNil()      => BigInt(0)
      case KCons(h, t) =>
        (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
    }
  } ensuring {
    _ == this.filter(p).size
  }
}

@library
object KListOps {

  /**
   * Obtain a new list by removing the the first occurrence
   * of e from list.
   */
  def delete[V] (list: KList[V], e: Item[V]): KList[V] = list.delete(e)

  def permutation[V] (l1: KList[V], l2: KList[V]): Boolean = {
    if (l1 == KNil[V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res =>
    if (res) {
      l1.size == l2.size &&
        permutation(l2, l1) &&
        l1.content == l2.content
    } else {
      l1.size != l2.size &&
        !permutation(l2, l1) &&
        l1.content != l2.content
    }
  }
}

object KList {
  @ignore
  def apply[V] (elems: (BigInt, V)*): KList[V] = {
    var l: KList[V] = KNil[V]()
    for (e <- elems) {
      l = KCons(Item(e._1, e._2), l)
    }
    l.reverse
  }
}

// 'KCons' Extractor
object :: {
  @library
  def unapply[A] (l: KList[A]): Option[(Item[A], KList[A])] = l match {
    case KNil()       => None()
    case KCons(x, xs) => Some((x, xs))
  }
}
