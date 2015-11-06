package duck.spec

import leon.lang._
import leon.annotation._
import duck.collection._

case class EmptyArray[T] () extends FunctionalArray[T]
case class UpdatedArray[T] (a : FunctionalArray[T], i : BigInt, e : T) extends FunctionalArray[T]

sealed abstract class FunctionalArray[T] {
  def acc (i : BigInt) : Option[T] = {
    this match {
      case EmptyArray() => None()
      case UpdatedArray(a, j, e) if i == j => Some(e)
      case UpdatedArray(a, _, _) => a.acc(i)
    }
  }

  def upd (i : BigInt, e : T) : FunctionalArray[T] = {
    UpdatedArray(this, i, e)
  } ensuring {
    res => res.acc(i) == Some(e)
  }
}

sealed case class BoundedArray[T] (array : FunctionalArray[T], size : BigInt) {
  def acc (i : BigInt) : Option[T] = {
    require(i >= 0 && i < size)
    array.acc(i)
  }

  def upd (i : BigInt) (e : T) : BoundedArray[T] = {
    require(i >= 0 && i < size)
    BoundedArray(array.upd(i, e), size)
  } ensuring {
    res => res.acc(i) == Some(e)
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
  def resize_eq[T] (a : BoundedArray[T], i : BigInt, j : BigInt) : Boolean = {
    require(a.size >= 0 && i >= 0 && j >= 0 && j < i && j < a.size)
    a.resize(i).acc(j) == a.acc(j)
  } holds
}
