package duck.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import duck.collection._

case class EmptyArray[T] () extends FunctionalArray[T]
case class UpdatedArray[T] (a : FunctionalArray[T], i : BigInt, e : T) extends FunctionalArray[T]

sealed abstract class FunctionalArray[T] {

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0)
    this match {
      case EmptyArray() => None()
      case UpdatedArray(a, j, e) if i == j => Some(e)
      case UpdatedArray(a, _, _) => a.acc(i)
    }
  }

  def upd (i : BigInt, e : T) : FunctionalArray[T] = {
    require(i >= 0)
    UpdatedArray(this, i, e)
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def srlAt (i : BigInt, n : BigInt) : FunctionalArray[T] = {
    require(i >= 0 && n >= 0)
    this match {
      case EmptyArray() => EmptyArray()
      case UpdatedArray(a, j, e) if j >= i => UpdatedArray(a.srlAt(i, n), j + n, e)
      case UpdatedArray(a, j, e) => UpdatedArray(a.srlAt(i, n), j, e)
    }
  }

  def srl (n : BigInt) : FunctionalArray[T] = {
    require(n >= 0)
    srlAt(0, n)
  }

  def sll (n : BigInt) : FunctionalArray[T] = {
    require(n >= 0)
    this match {
      case EmptyArray() => EmptyArray()
      case UpdatedArray(a, j, e) if j < n => a.sll(n)
      case UpdatedArray(a, j, e) => UpdatedArray(a.sll(n), j - n, e)
    }
  }

}

object FunctionalArray {

  def empty[T] : FunctionalArray[T] = EmptyArray()

}

object FunctionalArrayLemmas {

  def acc_upd_eq[T] (a : FunctionalArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : FunctionalArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && j >= 0 && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  @induct
  def acc_srl[T] (a : FunctionalArray[T], n : BigInt, i : BigInt) = {
    require(n >= 0 && i >= 0)
    a.srl(n).acc(i + n) == a.acc(i)
  } holds

  @induct
  def acc_sll[T] (a : FunctionalArray[T], n : BigInt, i : BigInt) = {
    require(n >= 0 && i >= 0)
    a.sll(n).acc(i) == a.acc(i + n)
  } holds

}

sealed case class BoundedArray[T] (array : FunctionalArray[T], size : BigInt) {

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    array.acc(i)
  }

  def upd (i : BigInt, e : T) : BoundedArray[T] = {
    require(i >= 0 && i < size)
    BoundedArray(array.upd(i, e), size)
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def srl (n : BigInt) : BoundedArray[T] = BoundedArray(array.srl(n), size + n)

  def sll (n : BigInt) : BoundedArray[T] = {
    require(n >= 0 && n <= size)
    BoundedArray(array.sll(n), size - n)
  }

  def resize (i : BigInt) = {
    require(i >= 0)
    BoundedArray(array, i)
  }

}

object BoundedArray {

  def empty[T] : BoundedArray[T] = BoundedArray(EmptyArray(), 0)

  def alloc[T] (size : BigInt) : BoundedArray[T] = BoundedArray(EmptyArray(), size)

}

object BoundedArrayLemmas {

  def acc_upd_eq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && i < a.size && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : BoundedArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && i < a.size && j >= 0 && j < a.size && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  def resize_eq[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.size >= 0 && i >= 0 && j >= 0 && j < i && j < a.size)
    a.resize(i).acc(j) == a.acc(j)
  } holds

  def acc_srl[T] (a : BoundedArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0 && j < a.size)
    a.srl(i).acc(i + j) == a.acc(j) because {
      FunctionalArrayLemmas.acc_srl(a.array, i, j)
    }
  } holds

  def acc_sll[T] (a : BoundedArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0 && j < a.size - i)
    a.sll(i).acc(j) == a.acc(i + j) because {
      FunctionalArrayLemmas.acc_sll(a.array, i, j)
    }
  } holds

}

sealed case class ListArray[T] (list : List[(BigInt, T)]) {

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0)
    list match {
      case Nil() => None()
      case Cons((j, v), tl) if i == j => Some(v)
      case Cons(_, tl) => ListArray(tl).acc(i)
    }
  }

  def upd (i : BigInt, e : T) : ListArray[T] = {
    require(i >= 0)
    ListArray(Cons((i, e), list))
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def srlAt (i : BigInt, n : BigInt) : ListArray[T] = {
    require(i >= 0 && n >= 0)
    list match {
      case Nil() => ListArray(Nil())
      case Cons((j, v), tl) if j >= i => ListArray(Cons((j + n, v), ListArray(tl).srlAt(i, n).list))
      case Cons((j, v), tl) => ListArray(Cons((j, v), ListArray(tl).srlAt(i, n).list))
    }
  }

  def srl (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    srlAt(0, n)
  }

  def sll (n : BigInt) : ListArray[T] = {
    require(n >= 0)
    list match {
      case Nil() => ListArray(Nil())
      case Cons((j, v), tl) if j < n => ListArray(tl).sll(n)
      case Cons((j, v), tl) => ListArray(Cons((j - n, v), ListArray(tl).sll(n).list))
    }
  }

}

object ListArray {

  def empty[T] : ListArray[T] = ListArray(Nil())

}

object ListArrayLemmas {

  def acc_upd_eq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : ListArray[T], i : BigInt, e : T, j : BigInt) : Boolean = {
    require(i >= 0 && j >= 0 && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  def acc_srl[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && i >= 0)
    a.srl(n).acc(i + n) == a.acc(i) because {
      a.list match {
        case Nil() => trivial
        case Cons((j, v), tl) if i == j => trivial
        case Cons((j, v), tl) => acc_srl(ListArray(tl), n, i)
      }
    }
  } holds

  def acc_sll[T] (a : ListArray[T], n : BigInt, i : BigInt) : Boolean = {
    require(n >= 0 && i >= 0)
    a.sll(n).acc(i) == a.acc(i + n) because {
      a.list match {
        case Nil() => trivial
        case Cons((j, v), tl) if j == i + n => trivial
        case Cons((j, v), tl) => acc_sll(ListArray(tl), n, i)
      }
    }
   } holds

}

sealed case class BoundedListArray[T] (array : ListArray[T], size : BigInt) {

  def acc (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    array.acc(i)
  }

  def upd (i : BigInt, e : T) : BoundedListArray[T] = {
    require(i >= 0 && i < size)
    BoundedListArray(array.upd(i, e), size)
  } ensuring {
    res => res.acc(i) == Some(e)
  }

  def srl (n : BigInt) : BoundedListArray[T] = BoundedListArray(array.srl(n), size + n)

  def sll (n : BigInt) : BoundedListArray[T] = {
    require(n >= 0 && n <= size)
    BoundedListArray(array.sll(n), size - n)
  }

  def resize (i : BigInt) = {
    require(i >= 0)
    BoundedListArray(array, i)
  }

}

object BoundedListArray {

  def empty[T] : BoundedListArray[T] = BoundedListArray(ListArray.empty, 0)

  def alloc[T] (size : BigInt) : BoundedListArray[T] = BoundedListArray(ListArray.empty, size)

}

object BoundedListArrayLemmas {

  def acc_upd_eq[T] (a : BoundedListArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && i < a.size && i == j)
    a.upd(i, e).acc(j) == Some(e)
  } holds

  def acc_upd_neq[T] (a : BoundedListArray[T], i : BigInt, e : T, j : BigInt) = {
    require(i >= 0 && i < a.size && j >= 0 && j < a.size && i != j)
    a.upd(i, e).acc(j) == a.acc(j)
  } holds

  def resize_eq[T] (a : BoundedListArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.size >= 0 && i >= 0 && j >= 0 && j < i && j < a.size)
    a.resize(i).acc(j) == a.acc(j)
  } holds

  def acc_srl[T] (a : BoundedListArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0 && j < a.size)
    a.srl(i).acc(i + j) == a.acc(j) because {
      ListArrayLemmas.acc_srl(a.array, i, j)
    }
  } holds

  def acc_sll[T] (a : BoundedListArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0 && j < a.size - i)
    a.sll(i).acc(j) == a.acc(i + j) because {
      ListArrayLemmas.acc_sll(a.array, i, j)
    }
  } holds

}
