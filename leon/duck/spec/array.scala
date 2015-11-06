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

  def srl (i : BigInt) : FunctionalArray[T] = {
    require(i >= 0)
    this match {
      case EmptyArray() => EmptyArray()
      case UpdatedArray(a, j, e) => UpdatedArray(a.srl(i), j + i, e)
    }
  }

  def sll (i : BigInt) : FunctionalArray[T] = {
    require(i >= 0)
    this match {
      case EmptyArray() => EmptyArray()
      case UpdatedArray(a, j, e) if j < i => a.sll(i)
      case UpdatedArray(a, j, e) => UpdatedArray(a.sll(i), j - i, e)
    }
  }
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
  def acc_srl[T] (a : FunctionalArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0)
    a.srl(i).acc(i + j) == a.acc(j)
  } holds

  @induct
  def acc_sll[T] (a : FunctionalArray[T], i : BigInt, j : BigInt) = {
    require(i >= 0 && j >= 0)
    a.sll(i).acc(j) == a.acc(i + j)
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

  def srl (i : BigInt) : BoundedArray[T] = BoundedArray(array.srl(i), size + i)

  def sll (i : BigInt) : BoundedArray[T] = {
    require(i >= 0 && i <= size)
    BoundedArray(array.sll(i), size - i)
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
