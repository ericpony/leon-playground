package duck.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import duck.collection._
import duck.spec.ListLemmas._

case class EmptyArray[K, V] () extends FunctionalArray[K, V]
case class UpdatedArray[K, V] (a : FunctionalArray[K, V], i : K, e : V) extends FunctionalArray[K, V]

sealed abstract class FunctionalArray[K, V] {

  def acc (i : K) : Option[V] = {
    this match {
      case EmptyArray() => None()
      case UpdatedArray(a, j, e) if i == j => Some(e)
      case UpdatedArray(a, _, _) => a.acc(i)
    }
  }

  def upd (i : K, e : V) : FunctionalArray[K, V] = {
    UpdatedArray(this, i, e)
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def domain : Set[K] = {
    this match {
      case EmptyArray() => Set.empty
      case UpdatedArray(a, i, e) => Set(i) ++ a.domain
    }
  }

}

object FunctionalArray {

  def empty[K, V] : FunctionalArray[K, V] = EmptyArray()

}

object FunctionalArrayLemmas {

  def acc_upd_eq[K, V] (a : FunctionalArray[K, V], i : K, e : V, j : K) = {
    require(i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[K, V] (a : FunctionalArray[K, V], i : K, e : V, j : K) = {
    require(i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  @induct
  def acc_in_domain[K, V] (a : FunctionalArray[K, V], i : K) = {
    require(a.domain.contains(i))
    a.acc(i) match {
      case None() => false
      case Some(e) => true
    }
  } holds

  @induct
  def acc_out_domain[K, V] (a : FunctionalArray[K, V], i : K) = {
    require(!a.domain.contains(i))
    a.acc(i) == None[V]()
  } holds

}


sealed case class BoundedArray[T] (array : FunctionalArray[BigInt, T], size : BigInt) {

  def acc (i : BigInt) : Option[T] = {
    require(inv && vi(i))
    array.acc(i)
  }

  def upd (i : BigInt, e : T) : BoundedArray[T] = {
    require(inv && vi(i))
    BoundedArray(array.upd(i, e), size)
  } ensuring {
    res => res.inv && res.acc(i) == Some(e)
  }

  def srl (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), size + n)
      case UpdatedArray(a, i, e) => BoundedArray(UpdatedArray(BoundedArray(a, size).srl(n).array, i + n, e), size + n)
    }
  } ensuring {
    res => res.inv && res.size == size + n
  }

  def sll (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0 && n <= size)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), size - n)
      case UpdatedArray(a, i, e) if i < n => BoundedArray(a, size).sll(n)
      case UpdatedArray(a, i, e) => BoundedArray(UpdatedArray(BoundedArray(a, size).sll(n).array, i - n, e) , size - n)
    }
  } ensuring {
    res => res.inv && res.size == size - n
  }

  def resize (n : BigInt) : BoundedArray[T] = {
    require(inv && n >= 0)
    array match {
      case EmptyArray() => BoundedArray(EmptyArray[BigInt, T](), n)
      case UpdatedArray(a, i, e) if i < n => BoundedArray(UpdatedArray(BoundedArray(a, size).resize(n).array, i, e), n)
      case UpdatedArray(a, i, e) => BoundedArray(a, size).resize(n)
    }
  } ensuring {
    res => res.inv && res.size == n
  }

  def vi (i : BigInt) : Boolean = {
    i >= 0 && i < size
  }

  def inv : Boolean = {
    size >= 0 && BoundedArray.domain_in_range(array, 0, size - 1)
  }

}

object BoundedArray {

  def empty[T] : BoundedArray[T] = BoundedArray(EmptyArray(), 0)

  def alloc[T] (size : BigInt) : BoundedArray[T] = BoundedArray(EmptyArray(), size)

  def domain_in_range[T] (array : FunctionalArray[BigInt, T], min : BigInt, max : BigInt) : Boolean = {
    array match {
      case EmptyArray() => true
      case UpdatedArray(a, i, e) => i >= min && i <= max && domain_in_range(a, min, max)
    }
  }

}
object BoundedArrayLemmas {

  def acc_upd_eq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && a.vi(j) && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  def acc_srl[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.inv && i >= 0 && j >= 0 && j < a.size)
    a.srl(i).acc(i + j) == a.acc(j) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, k, e) if k == j => trivial
        case UpdatedArray(b, k, e) => acc_srl(BoundedArray(b, a.size), i, j)
      }
    }
  } holds

  def acc_sll[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.inv && i >= 0 && j >= 0 && j < a.size - i)
    a.sll(i).acc(j) == a.acc(i + j) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, k, e) if k == i + j => trivial
        case UpdatedArray(b, k, e) => acc_sll(BoundedArray(b, a.size), i, j)
      }
    }
  } holds

  def acc_resize[T] (a : BoundedArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(a.inv && a.vi(i) && n >= 0 && i < n)
    a.resize(n).acc(i) == a.acc(i) because {
      a.array match {
        case EmptyArray() => trivial
        case UpdatedArray(b, j, e) if j == i => trivial
        case UpdatedArray(b, j, e) => acc_resize(BoundedArray(b, a.size), n, i)
      }
    }
  } holds

}

sealed case class ListArray[T] (array : List[Option[T]]) {

  def apply (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    acc(i)
  }

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    array(i)
  }

  def upd (i : BigInt, e : T) : ListArray[T] = {
    require(i >= 0 && i < size)
    ListArray(array.updated(i, Some(e)))
  } ensuring {
    res => res.size == size && res.acc(i) == Some(e) because {
      ListLemmas.acc_updated_eq(array, i, Some(e), i)
    }
  }

  def size : BigInt = array.size

  def :+ (e : T) : ListArray[T] = {
    ListArray(array :+ Some(e))
  } ensuring {
    res => res.size == size + 1
  }

  def ++ (that : ListArray[T]) : ListArray[T] = {
    ListArray(array ++ that.array)
  } ensuring {
    res => res.size == size + that.size
  }

  def append (e : T) : ListArray[T] = {
    this :+ e
  } ensuring {
    res => res.size == size + 1
  }

  def append (that : ListArray[T]) : ListArray[T] = {
    this ++ that
  } ensuring {
    res => res.size == size + that.size
  }

  def shift (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    if (n == 0)
      this
    else
      ListArray(Cons(None[T](), shift(n - 1).array))
  } ensuring {
    res => res.size == size + n
  }

  def drop (n : BigInt) : ListArray[T] = {
    ListArray(array.drop(n))
  } ensuring {
    res => res.size == (
      if (n <= 0) size
      else if (n >= size) BigInt(0)
      else size - n
    )
  }

  def take (n : BigInt) : ListArray[T] = {
    ListArray(array.take(n))
  } ensuring {
    res => res.size == (
      if (n <= 0) BigInt(0)
      else if (n >= size) size
      else n
    )
  }

  def slice (from : BigInt, until : BigInt) : ListArray[T] = {
    require(from >= 0 && until >= from && until <= size)
    ListArray(array.slice(from, until))
  }

  def forall (p : Option[T] => Boolean) : Boolean = {
    array.forall(p)
  }

  def exists (p : Option[T] => Boolean) : Boolean = {
    array.exists(p)
  }

  def toList : List[T] = {
    array match {
      case Nil() => Nil[T]()
      case Cons(None(), tl) => ListArray(tl).toList
      case Cons(Some(hd), tl) => Cons(hd, ListArray(tl).toList)
    }
  }

}

object ListArray {

  @ignore
  def apply[T] (elems : T*) : ListArray[T] = {
    var l : ListArray[T] = ListArray.alloc[T](elems.size)
    var i = 0
    for (e <- elems) {
      l = l.upd(i, e)
      i = i + 1
    }
    l
  }

  def empty[T] : ListArray[T] = {
    ListArray[T](Nil[Option[T]]())
  } ensuring {
    res => res.size == 0
  }

  def alloc[T] (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    if (n == 0)
      ListArray(Nil[Option[T]]())
    else
      ListArray(Cons(None[T](), ListArray.alloc[T](n - 1).array))
  } ensuring {
    res => res.size == n && res.array.forall(e => !e.isDefined)
  }

}

object ListArrayLemmas {

  def acc_upd_eq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && j >= 0 && j < a.size && i != j)
    a.upd(i, e).acc(j) == a.acc(j) because ListLemmas.acc_updated_neq(a.array, i, Some(e), j)
  } holds

  def acc_append1[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a1.size)
      (a1 ++ a2).acc(i) == a1.acc(i) because {
        a1.array match {
          case Nil() => i == 0
          case Cons(hd, tl) if i == 0 => trivial
          case Cons(hd, tl) => acc_append1(ListArray(tl), a2, i - 1)
        }
      }
  } holds

  def acc_append1[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i >= 0 && i < a.size)
      (a :+ e).acc(i) == a.acc(i) because {
        a.array match {
          case Nil() => i == 0
          case Cons(hd, tl) if i == 0 => trivial
          case Cons(hd, tl) => acc_append1(ListArray(tl), e, i - 1)
        }
      }
  } holds

  def acc_append2[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a2.size)
      (a1 ++ a2).acc(a1.size + i) == a2.acc(i) because {
        a1.array match {
          case Nil() => trivial
          case Cons(hd, tl) => acc_append2(ListArray(tl), a2, i)
        }
      }
  } holds

  def acc_append2[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i == a.size)
      (a :+ e).acc(i) == Some(e) because {
        a.array match {
          case Nil() => trivial
          case Cons(hd, tl) => acc_append2(ListArray(tl), e, i - 1)
        }
      }
  } holds

  def acc_append[T] (a1 : ListArray[T], a2 : ListArray[T], i : BigInt) : Boolean = {
    require(i >= 0 && i < a1.size + a2.size)
    if (i < a1.size)
      (a1 ++ a2).acc(i) == a1.acc(i) because acc_append1(a1, a2, i)
    else
      (a1 ++ a2).acc(i) == a2.acc(i - a1.size) because acc_append2(a1, a2, i - a1.size)
  } holds

  def acc_append[T] (a : ListArray[T], e : T, i : BigInt) : Boolean = {
    require(i >= 0 && i <= a.size)
    if (i < a.size)
      (a :+ e).acc(i) == a.acc(i) because acc_append1(a, e, i)
    else
      (a :+ e).acc(i) == Some(e) because acc_append2(a, e, i)
  } holds

  def acc_shift[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && i >= 0 && i < a.size)
    a.shift(n).acc(i + n) == a.acc(i) because {
      if (n == 0) {
        trivial
      } else {
        acc_shift(a, n - 1, i)
      }
    }
  } holds

  def acc_drop[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && n <= a.size && i >= 0 && i < a.size - n)
    a.drop(n).acc(i) == a.acc(i + n) because ListLemmas.acc_drop(a.array, n, i)
   } holds

  def acc_take[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(i >= 0 && i < a.size && i < n)
    a.take(n).acc(i) == a.acc(i) because ListLemmas.acc_take(a.array, n, i)
  } holds

  def shift_append_eq[T] (a : ListArray[T], n : BigInt) : Boolean = {
    require(n >= 0)
    a.shift(n) == ListArray.alloc(n) ++ a because {
      if (n == 0)
        trivial
      else
        shift_append_eq(a, n - 1)
    }
  } holds

  def append_drop_eq[T] (a1 : ListArray[T], a2 : ListArray[T]) : Boolean = {
    (a1 ++ a2).drop(a1.size) == a2 because appendTakeDrop(a1.array, a2.array, a1.size)
  } holds

  def shift_drop_eq[T] (a : ListArray[T], n : BigInt) : Boolean = {
    require (n >= 0)
    a.shift(n).drop(n) == a because {
      shift_append_eq(a, n) && append_drop_eq(ListArray.alloc(n), a)
    }
  } holds

  def append_forall[T] (a : ListArray[T], e : T, p : Option[T] => Boolean) : Boolean = {
    require(a.array.forall(p) && p(Some(e)))
    (a :+ e).forall(p) because ListLemmas.append_forall(a.array, Some(e), p)
  } holds

  def append_forall[T] (a1 : ListArray[T], a2 : ListArray[T], p : Option[T] => Boolean) : Boolean = {
    require(a1.array.forall(p) && a2.array.forall(p))
    (a1 ++ a2).forall(p) because ListLemmas.append_forall(a1.array, a2.array, p)
  } holds

}
