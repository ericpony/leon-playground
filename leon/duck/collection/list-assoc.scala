package duck.collection

import duck.proof.sugar._
import duck.proof.KListLemmas._
import leon.proof._
import leon.lang._
import leon.annotation._

/**
  * KList
  * List of key-value pairs with integer keys
  */
package object KList {

  case class Item[K, V] (key : K, value : V)

  case class KCons[K, V] (h : Item[K, V], t : KList[K, V]) extends KList[K, V]

  case class KNil[K, V] () extends KList[K, V]

  @library
  sealed abstract class KList[K, V] {

    def size : BigInt = (this match {
      case KNil() => BigInt(0)
      case KCons(h, t) => 1 + t.size
    }) ensuring (_ >= 0)

    def content : Set[Item[K, V]] = this match {
      case KNil() => Set[Item[K, V]]()
      case KCons(h, t) => Set(h) ++ t.content
    }

    def contains (v : Item[K, V]) : Boolean = (this match {
      case KCons(h, t) if h == v => true
      case KCons(_, t) => t.contains(v)
      case KNil() => false
    }) ensuring {
      _ == (content contains v) && hasKey(v.key)
    }

    def ++ (that : KList[K, V]) : KList[K, V] = (this match {
      case KNil() => that
      case KCons(x, xs) => KCons[K, V](x, xs ++ that)
    }) ensuring { res =>
      (res.content == this.content ++ that.content) &&
        (res.size == this.size + that.size) &&
        (that != KNil[K, V]() || res == this)
    }

    def head : Item[K, V] = {
      require(this != KNil[K, V]())
      val KCons(h, _) = this
      h
    }

    def tail : KList[K, V] = {
      require(this != KNil[K, V]())
      val KCons(_, t) = this
      t
    }

    def :: (t : Item[K, V]) : KList[K, V] = KCons(t, this)

    def :+ (t : Item[K, V]) : KList[K, V] = {
      this match {
        case KNil() => KCons(t, this)
        case KCons(x, xs) => KCons(x, xs :+ (t))
      }
    } ensuring (res => (res.size == size + 1) && (res.content == content ++ Set(t)))

    def reverse : KList[K, V] = {
      this match {
        case KNil() => this
        case KCons(x, xs) => xs.reverse :+ x
      }
    } ensuring (res => (res.size == size) && (res.content == content))

    def keys : List[K] = mapList(item => item.key)

    def values : List[V] = mapList(item => item.value)

    def take (i : BigInt) : KList[K, V] = {
      (this, i) match {
        case (KNil(), _) => KNil[K, V]()
        case (KCons(h, t), i) => if (i <= BigInt(0)) KNil[K, V]() else KCons(h, t.take(i - 1))
      }
    } ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if (i <= 0) BigInt(0)
        else if (i >= this.size) this.size
        else i
        ))
    }

    def drop (i : BigInt) : KList[K, V] = {
      (this, i) match {
        case (KNil(), _) => KNil[K, V]()
        case (KCons(h, t), i) => if (i <= BigInt(0)) KCons[K, V](h, t) else t.drop(i - 1)
      }
    } ensuring { res =>
      res.content.subsetOf(this.content) && (res.size == (
        if (i <= 0) this.size
        else if (i >= this.size) BigInt(0)
        else this.size - i
        ))
    }

    def slice (from : BigInt, to : BigInt) : KList[K, V] = {
      require(0 <= from && from <= to && to <= size)
      drop(from).take(to - from)
    }

    def replace (from : Item[K, V], to : Item[K, V]) : KList[K, V] = {
      this match {
        case KNil() => KNil[K, V]()
        case KCons(h, t) =>
          val r = t.replace(from, to)
          if (h == from) KCons(to, r) else KCons(h, r)
      }
    } ensuring { (res : KList[K, V]) =>
      res.size == this.size &&
        res.content == (
          (this.content -- Set(from)) ++
            (if (this.content contains from) Set(to) else Set[Item[K, V]]())
          )
    }

    /**
      * Delete ALL occurrences of e from the list
      */
    def - (e : Item[K, V]) : KList[K, V] = {
      this match {
        case KCons(h, t) => if (e == h) t - e else KCons(h, t - e)
        case KNil() => KNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == this.content -- Set(e)
    }

    def -- (that : KList[K, V]) : KList[K, V] = {
      this match {
        case KCons(h, t) => if (that.contains(h)) t -- that else KCons(h, t -- that)
        case KNil() => KNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == this.content -- that.content
    }

    def & (that : KList[K, V]) : KList[K, V] = {
      this match {
        case KCons(h, t) => if (that.contains(h)) KCons(h, t & that) else t & that
        case KNil() => KNil[K, V]()
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content == (this.content & that.content)
    }

    def ~ (that : KList[K, V]) = permutation(this, that)

    def ~~ (that : KList[K, V]) = this.content == that.content

    def update (data : Item[K, V]) : KList[K, V] = {
      if (!hasKey(data.key))
        data :: this
      else {
        this match {
          case KNil() => data :: KNil[K, V]()
          case KCons(Item(k, v), t) =>
            if (k == data.key) Item(k, data.value) :: t
            else Item(k, v) :: t.update(data)
        }
      }
    } ensuring {
      res => res.size > 0 && res.hasKey(data.key)
      //res.forall(p => p.key != data.key || p.value == data.value)
    }

    def hasKey (key : K) : Boolean = {
      this match {
        case KNil() => false
        case KCons(Item(k, v), t) => k == key || t.hasKey(key)
      }
    } ensuring {
      res => {
        res implies
          get(key).isDefined &&
            // Adding the following line will lead to unsoundness
            // contains(get(key).get) &&
            getAll(key) != KNil[K, V]()
      } and {
        !res implies
          !get(key).isDefined &&
            getAll(key) == KNil[K, V]()
      }
    }

    /**
      * Get the first element in this list with the provided key.
      */
    def getFirst (key : K) : Option[Item[K, V]] = {
      this match {
        case KNil() => None[Item[K, V]]()
        case KCons(h, t) => if (h.key == key) Some[Item[K, V]](h) else t.getFirst(key)
      }
    } ensuring { res =>
      res.isDefined implies
        res.get.key == key &&
          res.get == getAll(key).head
    }

    /**
      * Get the last element in this list with the provided key.
      */
    def getLast (key : K) = this.reverse.getFirst(key)

    /**
      * Get all elements in this list with the provided key.
      * The order in which the elements are stored in the returned list
      * is consistent with the order they are stored in the original list.
      * Note: This version of getAll is easier to verify for Leon than
      * the concise version
      * def getAll (key: K) = this.filter(item => item.key == key).
      */
    def getAll (key : K) : KList[K, V] = {
      this match {
        case KNil() => KNil[K, V]()
        case KCons(h, t) => if (h.key == key) KCons(h, t.getAll(key)) else t.getAll(key)
      }
    } ensuring { res =>
      res.size <= size and
        res.content.subsetOf(content) and
        res.forall(item => item.key == key) and
        (res != KNil[K, V]() implies hasKey(key))
    }

    /**
      * Get an element from the list with the provided key.
      */
    def get = getFirst _

    /**
      * Obtain a new list by removing the first occurrence of e
      * from this list.
      */
    def deleteFirst (e : Item[K, V]) : KList[K, V] = {
      if (this == KNil[K, V]()) this
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
    def deleteFirst (key : K) : KList[K, V] = {
      this match {
        case KNil() => this
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
    def deleteLast (key : K) = this.reverse.deleteFirst(key)

    /**
      * Obtain a new list by removing all element with the
      * provided key from this list.
      */
    def deleteAll (key : K) : KList[K, V] = {
      this match {
        case KNil() => this
        case KCons(h, t) => if (h.key == key) t.deleteAll(key) else KCons(h, t.deleteAll(key))
      }
    } ensuring { res =>
      res.size <= this.size and
        res.content.subsetOf(this.content) and
        res.forall(item => item.key != key)
    }

    def deleteAll (e : Item[K, V]) = this - e

    def delete (key : K) = deleteFirst(key)

    def delete (e : Item[K, V]) = deleteFirst(e)

    def init : KList[K, V] = {
      require(!isEmpty)
      ((this : @unchecked) match {
        case KCons(h, KNil()) =>
          KNil[K, V]()
        case KCons(h, t) =>
          KCons[K, V](h, t.init)
      })
    } ensuring { (r : KList[K, V]) =>
      r.size == this.size - 1 &&
        r.content.subsetOf(this.content)
    }

    def last : Item[K, V] = {
      require(!isEmpty)
      (this : @unchecked) match {
        case KCons(h, KNil()) => h
        case KCons(_, t) => t.last
      }
    } ensuring { this.contains _ }

    def lastOption : Option[Item[K, V]] = {
      this match {
        case KCons(h, t) => t.lastOption.orElse(Some(h))
        case KNil() => None[Item[K, V]]()
      }
    } ensuring { _.isDefined != this.isEmpty }

    def headOption : Option[Item[K, V]] = {
      this match {
        case KCons(h, t) => Some(h)
        case KNil() => None[Item[K, V]]()
      }
    } ensuring { _.isDefined != this.isEmpty }

    def unique : KList[K, V] = this match {
      case KNil() => KNil()
      case KCons(h, t) => KCons(h, t.unique - h)
    }

    def rotate (s : BigInt) : KList[K, V] = {
      if (isEmpty) KNil[K, V]()
      else drop(s mod size) ++ take(s mod size)
    } ensuring {
      res => res.size == this.size
    }

    def isEmpty = this match {
      case KNil() => true
      case _ => false
    }

    // Higher-order API
    def map[K2, V2] (f : Item[K, V] => Item[K2, V2]) : KList[K2, V2] = {
      this match {
        case KNil() => KNil[K2, V2]()
        case KCons(h, t) => f(h) :: t.map(f)
      }
    } ensuring { _.size == this.size }

    def mapList[V2] (f : Item[K, V] => V2) : List[V2] = {
      this match {
        case KNil() => Nil[V2]()
        case KCons(h, t) => f(h) :: t.mapList(f)
      }
    } ensuring { _.size == this.size }

    def foldLeft[V2] (z : V2)(f : (V2, Item[K, V]) => V2) : V2 = this match {
      case KNil() => z
      case KCons(h, t) => t.foldLeft(f(z, h))(f)
    }

    def foldRight[V2] (z : V2)(f : (Item[K, V], V2) => V2) : V2 = this match {
      case KNil() => z
      case KCons(h, t) => f(h, t.foldRight(z)(f))
    }

    def scanLeft[K2, V2] (z : Item[K2, V2])(f : (Item[K2, V2], Item[K, V]) => Item[K2, V2]) : KList[K2, V2] = {
      this match {
        case KNil() => z :: KNil[K2, V2]()
        case KCons(h, t) => z :: t.scanLeft(f(z, h))(f)
      }
    } ensuring { !_.isEmpty }

    def scanRight[K2, V2] (z : Item[K2, V2])(f : (Item[K, V], Item[K2, V2]) => Item[K2, V2]) : KList[K2, V2] = {
      this match {
        case KNil() => z :: KNil[K2, V2]()
        case KCons(h, t) =>
          val rest@KCons(h1, _) = t.scanRight(z)(f)
          f(h, h1) :: rest
      }
    } ensuring { !_.isEmpty }

    def filter (p : Item[K, V] => Boolean) : KList[K, V] = {
      this match {
        case KNil() => KNil[K, V]()
        case KCons(h, t) if p(h) => KCons(h, t.filter(p))
        case KCons(_, t) => t.filter(p)
      }
    } ensuring { res =>
      res.size <= this.size &&
        res.content.subsetOf(this.content) &&
        res.forall(p)
    }

    def filterNot (p : Item[K, V] => Boolean) : KList[K, V] =
      filter(!p(_)) ensuring { res =>
        res.size <= this.size &&
          res.content.subsetOf(this.content) &&
          res.forall(!p(_))
      }

    def partition (p : Item[K, V] => Boolean) : (KList[K, V], KList[K, V]) = {
      this match {
        case KNil() => (KNil[K, V](), KNil[K, V]())
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
    def withFilter (p : Item[K, V] => Boolean) = filter(p)

    def forall (p : Item[K, V] => Boolean) : Boolean = this match {
      case KNil() => true
      case KCons(h, t) => p(h) && t.forall(p)
    }

    def exists (p : Item[K, V] => Boolean) = !forall(!p(_))

    def find (p : Item[K, V] => Boolean) : Option[Item[K, V]] = {
      this match {
        case KNil() => None[Item[K, V]]()
        case KCons(h, t) if p(h) => Some(h)
        case KCons(_, t) => t.find(p)
      }
    } ensuring { res =>
      res match {
        case Some(r) => (content contains r) && p(r)
        case None() => true
      }
    }

    def groupBy[K2] (f : Item[K, V] => K2) : Map[K2, KList[K, V]] = this match {
      case KNil() => Map.empty[K2, KList[K, V]]
      case KCons(h, t) =>
        val key : K2 = f(h)
        val rest : Map[K2, KList[K, V]] = t.groupBy(f)
        val prev : KList[K, V] = if (rest isDefinedAt key) rest(key) else KNil[K, V]()
        (rest ++ Map((key, h :: prev))) : Map[K2, KList[K, V]]
    }

    def takeWhile (p : Item[K, V] => Boolean) : KList[K, V] = {
      this match {
        case KCons(h, t) if p(h) => KCons(h, t.takeWhile(p))
        case _ => KNil[K, V]()
      }
    } ensuring { res =>
      (res forall p) &&
        (res.size <= this.size) &&
        (res.content subsetOf this.content)
    }

    def dropWhile (p : Item[K, V] => Boolean) : KList[K, V] = {
      this match {
        case KCons(h, t) if p(h) => t.dropWhile(p)
        case _ => this
      }
    } ensuring { res =>
      (res.size <= this.size) &&
        (res.content subsetOf this.content) &&
        (res.isEmpty || !p(res.head))
    }

    def count (p : Item[K, V] => Boolean) : BigInt = {
      this match {
        case KNil() => BigInt(0)
        case KCons(h, t) =>
          (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
      }
    } ensuring {
      _ == this.filter(p).size
    }
  }

  /* Obtain a new list by removing the the FIRST occurrence of e from list. */
  @library
  def delete[K, V] (list : KList[K, V], e : Item[K, V]) : KList[K, V] = list.delete(e)

  @library
  def permutation[K, V] (l1 : KList[K, V], l2 : KList[K, V]) : Boolean = {
    if (l1 == KNil[K, V]) {
      l1 == l2
    } else {
      val h1 = l1.head
      l2.contains(h1) && permutation(l1.tail, delete(l2, h1))
    }
  } ensuring { res =>
    if (res) {
      l1.size == l2.size &&
        l1.content == l2.content
    } else {
      l1.size != l2.size &&
        l1.content != l2.content
    }
  }

  @ignore
  def apply[K, V] (elems : (K, V)*) : KList[K, V] = {
    var l : KList[K, V] = KNil[K, V]()
    for (e <- elems) {
      l = KCons(Item(e._1, e._2), l)
    }
    l.reverse
  }

  // 'KCons' Extractor
  //  object :: {
  //    @library
  //    def unapply[K, V] (l: KList[K, V]): Option[(Item[K, V], KList[K, V])] = l match {
  //      case KNil()       => None()
  //      case KCons(x, xs) => Some((x, xs))
  //    }
  //  }

}
