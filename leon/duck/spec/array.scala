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

object IMap {

  def empty[T] = Map.empty[BigInt, T]

  def isDefinedBetween[T] (m : Map[BigInt, T], from : BigInt, until : BigInt) : Boolean = {
    if (from >= until)
      true
    else
      m.isDefinedAt(from) && isDefinedBetween(m, from + 1, until)
  }

  def isDefinedUntil[T] (m : Map[BigInt, T], n : BigInt) : Boolean = {
    isDefinedBetween(m, 0, n)
  }

  def defined_between_shrink[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, left : BigInt, right : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && left >= from && right <= until)
    isDefinedBetween(m, left, right) because {
      if (left >= right) trivial
      else if (left == from) defined_between_shrink(m, from + 1, until, left + 1, right)
      else defined_between_shrink(m, from + 1, until, left, right)
    }
  } holds

  def defined_between_tran[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    (
      (isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k)) ==> isDefinedBetween(m, i, k)
    ) because {
      if (isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k)) {
        if (i >= j) defined_between_shrink(m, j, k, i, k)
        else defined_between_tran(m, i + 1, j, k)
      } else trivial
    } &&
    (
      (isDefinedBetween(m, i, k) && j >= i && j <= k) ==> (isDefinedBetween(m, i, j) && isDefinedBetween(m, j, k))
    ) because {
      if ((isDefinedBetween(m, i, k) && j >= i && j <= k)) defined_between_shrink(m, i, k, i, j) && defined_between_shrink(m, i, k, j, k)
      else trivial
    }
  } holds

  def defined_between_at[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, i : BigInt) : Boolean = {
      require(i >= from && i < until && isDefinedBetween(m, from, until))
      m.isDefinedAt(i) because {
        if (from >= until) trivial
        else if (i == from) trivial
        else defined_between_at(m, from + 1, until, i)
      }
    } holds

  def defined_until_at[T] (m : Map[BigInt, T], n : BigInt, i : BigInt) : Boolean = {
    require(i >= 0 && i < n && isDefinedUntil(m, n))
    m.isDefinedAt(i) because defined_between_at(m, 0, n, i)
  } holds

  def updated_defined_at[T] (m : Map[BigInt, T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.isDefinedAt(j))
    m.updated(i, e).isDefinedAt(j)
  } holds

  def updated_defined_between[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until))
    isDefinedBetween(m.updated(i, e), from, until) because {
      if (from >= until) trivial
      else updated_defined_between(m, i, e, from + 1, until)
    }
  } holds

  def updated_defined_until[T] (m : Map[BigInt, T], i : BigInt, e : T, until : BigInt) : Boolean = {
    require(isDefinedUntil(m, until))
    isDefinedUntil(m.updated(i, e), until) because updated_defined_between(m, i, e, 0, until)
  } holds

  def updated_defined_between_extend[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until))
    if (i == from - 1) {
      isDefinedBetween(m.updated(i, e), i, until) because { updated_defined_between(m, i, e, from, until) }
    } else if (i == until) {
      isDefinedBetween(m.updated(i, e), from, i + 1) because {
        updated_defined_between(m, i, e, from, until) && defined_between_tran(m.updated(i, e), from, until, i + 1)
      }
    } else
      trivial
  } holds

  /* Assign */

  def assign_op[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Map[BigInt, T] = {
    if (from >= until) m
    else assign_op(m.updated(from, e), from + 1, until, e)
  }

  def assign_defined_between[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j))
    isDefinedBetween(assign_op(m, from, until, e), i, j) because {
      if (from >= until) trivial
      else {
        updated_defined_between(m, from, e, i, j) &&
        assign_defined_between(m.updated(from, e), from + 1, until, e, i, j)
      }
    }
  } holds

  def assign_defined_at[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt) : Boolean = {
    ((i >= from && i < until || m.isDefinedAt(i)) ==> assign_op(m, from, until, e).isDefinedAt(i)) because {
      if (i >= from && i < until) assign_defined_at(m.updated(from, e), from + 1, until, e, i)
      else if (m.isDefinedAt(i)) assign_defined_between(m, from, until, e, i, i + 1)
      else trivial
    }
  } holds

  private def assign_defined_between[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Boolean = {
    isDefinedBetween(assign_op(m, from, until, e), from, until) because {
      if (from >= until) trivial
      else {
        assign_defined_at(m.updated(from, e), from + 1, until, e, from) &&
        assign_defined_between(m.updated(from, e), from + 1, until, e)
      }
    }
  } holds

  def assign[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T) : Map[BigInt, T] = {
    assign_op(m, from, until, e)
  } ensuring { res =>
    isDefinedBetween(res, from, until) because assign_defined_between(m, from, until, e)
  }

  def acc_assign[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, e : T, i : BigInt) : Boolean = {
    require(assign_defined_at(m, from, until, e, i))
    if (i >= from && i < until) assign(m, from, until, e)(i) == e because {
      acc_assign(m.updated(from, e), from + 1, until, e, i)
    } else if (m.isDefinedAt(i)) assign(m, from, until, e)(i) == m(i) because {
      if (from >= until) assign(m, from, until, e)(i) == m(i)
      else updated_defined_at(m, from, e, i) && acc_assign(m.updated(from, e), from + 1, until, e, i)
    } else trivial
  } holds

  /* Copy */

  def can_copy[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until))
    if (from >= until) trivial
    else {
      defined_between_shrink(m, from, until, from + 1, until) &&
      updated_defined_between(m, from + n, m(from), from + 1, until)
    }
  } holds

  private def copy_op[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Map[BigInt, T] = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    if (from >= until) m2
    else copy_op(m1, m2.updated(from + n, m1(from)), from + 1, until, n)
  }

  def copy_defined_between[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n) && isDefinedBetween(m2, i, j))
    isDefinedBetween(copy_op(m1, m2, from, until, n), i, j) because {
      if (from >= until) trivial
      else {
        updated_defined_between(m2, from + n, m1(from), i, j) &&
        copy_defined_between(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i, j)
      }
    }
  } holds

  def copy_defined_at[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    if (i >= from + n && i < until + n) copy_op(m1, m2, from, until, n).isDefinedAt(i) because {
      copy_defined_at(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i)
    } else if (m2.isDefinedAt(i)) copy_op(m1, m2, from, until, n).isDefinedAt(i) because {
      copy_defined_between(m1, m2, from, until, n, i, i + 1)
    } else trivial
  } holds

  private def copy_defined_between[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    isDefinedBetween(copy_op(m1, m2, from, until, n), from + n, until + n) because {
      if (from >= until) trivial
      else {
        copy_defined_between(m1, m2.updated(from + n, m1(from)), from + 1, until, n) &&
        copy_defined_at(m1, m2.updated(from + n, m1(from)), from + 1, until, n, from + n)
      }
    }
  } holds

  def copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Map[BigInt, T] = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    copy_op(m1, m2, from, until, n)
  } ensuring { res =>
    isDefinedBetween(res, from + n, until + n) because {
      copy_defined_between(m1, m2, from, until, n)
    }
  }

  private def acc_copy_out[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && m2.isDefinedAt(i) && (i < from + n || i >= until + n) &&
      can_copy(m1, from, until, n) && copy_defined_at(m1, m2, from, until, n, i))
    copy(m1, m2, from, until, n)(i) == m2(i) because {
      if (from >= until) trivial
      else acc_copy_out(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i)
    }
  } holds

  private def acc_copy_in[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && i >= from + n && i < until + n &&
      can_copy(m1, from, until, n) && copy_defined_at(m1, m2, from, until, n, i) && defined_between_at(m1, from, until, i - n))
    copy(m1, m2, from, until, n)(i) == m1(i - n) because {
      if (i == from + n) acc_copy_out(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i)
      else acc_copy_in(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i)
    }
  } holds

  def acc_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    if (i >= from + n && i < until + n) acc_copy_in(m1, m2, from, until, n, i)
    else if (m2.isDefinedAt(i)) acc_copy_out(m1, m2, from, until, n, i)
    else trivial
  } holds

  /* To List */

  def toList[T] (m : Map[BigInt, T], from : BigInt, until : BigInt) : List[T] = {
    require(isDefinedBetween(m, from, until))
    if (from >= until) Nil[T]()
    else Cons(m(from), toList(m, from + 1, until))
  } ensuring { res =>
    res.size == (
      if (from <= until) until - from
      else BigInt(0)
    )
  }

  def acc_toList[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, i : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && i >= 0 && i < until - from && defined_between_at(m, from, until, i + from))
    toList(m, from, until)(i) == m(i + from) because {
      if (i == 0) trivial
      else acc_toList(m, from + 1, until, i - 1)
    }
  } holds

  def updated_toList[T] (m : Map[BigInt, T], i : BigInt, e : T, from : BigInt, until : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && (i < from || i >= until) && updated_defined_between(m, i, e, from, until))
    toList(m.updated(i, e), from, until) == toList(m, from, until) because {
      updated_toList(m, i, e, from + 1, until)
    }
  } holds

  def toList_cons[T] (m : Map[BigInt, T], i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i < j)
    Cons(m(i), toList(m, i + 1, j)) == toList(m, i, j)
  } holds

  def toList_snoc[T] (m : Map[BigInt, T], i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, j) && i < j && defined_between_shrink(m, i, j, i, j - 1) && defined_between_at(m, i, j, j - 1))
    toList(m, i, j - 1) :+ m(j - 1) == toList(m, i, j) because {
      if (i == j - 1) trivial
      else toList_snoc(m, i + 1, j)
    }
  } holds

  def toList_append[T] (m : Map[BigInt, T], i : BigInt, j : BigInt, k : BigInt) : Boolean = {
    require(isDefinedBetween(m, i, k) && i <= j && j <= k && defined_between_tran(m, i, j, k))
    toList(m, i, j) ++ toList(m, j, k) == toList(m, i, k) because {
      if (i == j) check{toList(m, i, j) ++ toList(m, j, k) == toList(m, i, k)}
      else toList_append(m, i + 1, j, k)
    }
  } holds

  def toList_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n))
    toList(copy(m1, m2, from, until, n), from + n, until + n) == toList(m1, from, until) because {
      if (from >= until) trivial
      else {
          toList_copy(m1, m2.updated(from + n, m1(from)), from + 1, until, n) &&
          acc_copy(m1, m2, from, until, n, from + n)
      }
    }
  } holds

  def toList_copy[T] (m1 : Map[BigInt, T], m2 : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt, i : BigInt, j : BigInt) : Boolean = {
    require(isDefinedBetween(m1, from, until) && can_copy(m1, from, until, n) && isDefinedBetween(m2, i, j) &&
      (i < from + n && j <= from + n || i >= until + n && j >= until + n || i >= j) && copy_defined_between(m1, m2, from, until, n, i, j))
    toList(copy(m1, m2, from, until, n), i, j) == toList(m2, i, j) because {
      if (from >= until || i >= j) check{toList(copy(m1, m2, from, until, n), i, j) == toList(m2, i, j)}
      else {
        check {
          acc_copy(m1, m2, from, until, n, i) &&
          toList_copy(m1, m2.updated(from + n, m1(from)), from + 1, until, n, i, j) &&
          updated_toList(m2, from + n, m1(from), i, j)
        }
      }
    }
  } holds

  def toList_drop[T] (m : Map[BigInt, T], from : BigInt, until : BigInt, n : BigInt) : Boolean = {
    require(isDefinedBetween(m, from, until) && n >= 0 && defined_between_shrink(m, from, until, from + n, until))
    toList(m, from, until).drop(n) == toList(m, from + n, until) because {
      if (from >= until || from + n >= until || n == 0) trivial
      else {
        defined_between_shrink(m, from, until, from + 1, until) &&
        toList_drop(m, from + 1, until, n - 1)
      }
    }
  } holds

}

sealed case class MapArray[T] (map : Map[BigInt, T], size : BigInt) {

  def :+ (e : T) : MapArray[T] = {
    require(inv)
    append(e)
  }

  def ++ (m : MapArray[T]) : MapArray[T] = {
    require(inv && m.inv)
    append(m)
  }

  def append (e : T) : MapArray[T] = {
    require(inv)
    MapArray(map.updated(size, e), size + 1)
  } ensuring { res =>
    res.size == size + 1 && res.inv because IMap.updated_defined_between_extend(map, size, e, 0, size)
  }

  def append (m : MapArray[T]) : MapArray[T] = {
    require(inv && m.inv)
    MapArray(IMap.copy(m.map, map, 0, m.size, size), size + m.size)
  } ensuring { res =>
    res.size == size + m.size && res.inv because {
      IMap.copy_defined_between(m.map, map, 0, m.size, size, 0, size) && IMap.defined_between_tran(res.map, 0, size, res.size)
    }
  }

  def apply (i : BigInt) : T = {
    require(inv && i >= 0 && i < size && IMap.defined_between_at(map, 0, size, i))
    map.apply(i)
  }

  def drop (n : BigInt) : MapArray[T] = {
    require(inv && ((n > 0 && n < size) ==> (IMap.defined_between_shrink(map, 0, size, n, size))))
    if (n <= 0) this
    else if (n >= size) MapArray.empty[T]
    else MapArray(IMap.copy(map, IMap.empty[T], n, size, -n), size - n)
  } ensuring { res =>
    res.size == (
      if (n <= 0) size
      else if (n >= size) BigInt(0)
      else size - n
    ) && res.inv
  }

  def isDefinedAt (i : BigInt) : Boolean = {
    map.isDefinedAt(i)
  }

  def isDefinedUntil (n : BigInt) : Boolean = {
    IMap.isDefinedUntil(map, n)
  }

  def prepend (e : T) : MapArray[T] = {
    require(inv)
    MapArray.create(1, e) ++ this
  } ensuring { res =>
    res.size == size + 1 && res.inv
  }

  def updated (i : BigInt, e : T) : MapArray[T] = {
    require(inv && i >= 0 && i < size)
    MapArray(map.updated(i, e), size)
  } ensuring { res =>
    res.size == size && res.inv because {
      IMap.updated_defined_until(map, i, e, size)
    }
  }

  def toList : List[T] = {
    require(inv)
    IMap.toList(map, 0, size)
  } ensuring { res =>
    res.size == size
  }

  def inv : Boolean = {
    size >= 0 && isDefinedUntil(size)
  }

}

object MapArray {

  def empty[T] : MapArray[T] = {
    MapArray(IMap.empty[T], 0)
  } ensuring { res =>
    res.size == 0 && res.inv
  }

  def create[T] (n : BigInt, e : T) : MapArray[T] = {
    require(n >= 0)
    MapArray(IMap.assign(IMap.empty[T], 0, n, e), n)
  } ensuring { res =>
    res.size == n && res.inv
  }

}

object MapArrayLemmas {

  def defined_until_at[T] (m : MapArray[T], n : BigInt, i : BigInt) : Boolean = {
      require(i >= 0 && i < n && m.isDefinedUntil(n))
      m.isDefinedAt(i) because IMap.defined_until_at(m.map, n, i)
    } holds

  def index_defined[T] (m : MapArray[T], i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size)
    m.isDefinedAt(i) because defined_until_at(m, m.size, i)
  } holds

  def acc_updated_eq[T] (m : MapArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && i == j)
    m.updated(i, e)(j) == e
  } holds

  def acc_updated_neq[T] (m : MapArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size && j >= 0 && j < m.size && i != j && index_defined(m, j))
    m.updated(i, e)(j) == m(j)
  } holds

  def acc_append[T] (m : MapArray[T], e : T, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i <= m.size)
    m.append(e)(i) == (
      if (i >= 0 && i < m.size) m(i)
      else e
    )
  } holds

  def acc_append[T] (m1 : MapArray[T], m2 : MapArray[T], i : BigInt) : Boolean = {
    require(m1.inv && m2.inv && i >= 0 && i < m1.size + m2.size)
    m1.append(m2)(i) == (
      if (i >= 0 && i < m1.size) m1(i)
      else m2(i - m1.size)
    ) because {
      IMap.acc_copy(m2.map, m1.map, 0, m2.size, m1.size, i)
    }
  } holds

  def acc_drop[T] (m : MapArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(m.inv)
    if (n <= 0 && i >= 0 && i < m.size) m.drop(n)(i) == m(i) because { index_defined(m, i) }
    else if (n > 0 && i >= 0 && i < m.size - n) m.drop(n)(i) == m(i + n) because {
      index_defined(m.drop(n), i) && IMap.acc_copy(m.map, IMap.empty[T], n, m.size, -n, i) && index_defined(m, i + n)
    } else trivial
  } holds

  def acc_prepend[T] (m : MapArray[T], e : T, i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i <= m.size)
    (if (i == 0) m.prepend(e)(i) == e
    else m.prepend(e)(i) == m(i - 1)) because {
      acc_append(MapArray.create(1, e), m, i)
    }
  } holds

  def acc_toList[T] (m : MapArray[T], i : BigInt) : Boolean = {
    require(m.inv && i >= 0 && i < m.size)
    m.toList(i) == m(i) because {
      IMap.acc_toList(m.map, 0, m.size, i)
    }
  } holds

  def append_toList[T] (m : MapArray[T], e : T) : Boolean = {
    require(m.inv)
      (m :+ e).toList == m.toList :+ e because {
        IMap.toList_snoc((m :+ e).map, 0, m.size + 1) &&
        IMap.updated_toList(m.map, m.size, e, 0, m.size)
      }
  } holds

  def append_toList[T] (m1 : MapArray[T], m2 : MapArray[T]) : Boolean = {
    require(m1.inv && m2.inv)
      (m1 ++ m2).toList == m1.toList ++ m2.toList because {
        if (m1.size == 0) IMap.toList_copy(m2.map, m1.map, 0, m2.size, m1.size)
        else {
          IMap.toList_append((m1 ++ m2).map, 0, m1.size, m1.size + m2.size) &&
          IMap.toList_copy(m2.map, m1.map, 0, m2.size, m1.size, 0, m1.size) &&
          IMap.toList_copy(m2.map, m1.map, 0, m2.size, m1.size)
        }
      }
  } holds

  def drop_toList[T] (m : MapArray[T], n : BigInt) : Boolean = {
    require(m.inv)
    m.drop(n).toList == m.toList.drop(n) because {
      if (n <= 0) trivial
      else {
        IMap.defined_between_shrink(m.map, 0, m.size, n, m.size) &&
        IMap.toList_copy(m.map, IMap.empty[T], n, m.size, -n) &&
        IMap.toList_drop(m.map, 0, m.size, n)
      }
    }
  } holds

  def prepend_toList[T] (m : MapArray[T], e : T) : Boolean = {
    require(m.inv)
    m.prepend(e).toList == Cons(e, m.toList) because {
      check {
        IMap.toList_append(m.prepend(e).map, 0, 1, m.size + 1) &&
        acc_prepend(m, e, 0) &&
        IMap.toList_copy(m.map, MapArray.create(1, e).map, 0, m.size, 1)
      }
    }
  } holds

}
