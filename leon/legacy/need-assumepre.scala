import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps

object Failed {

  def defined_between[T] (m : Map[BigInt, T], from : BigInt, until : BigInt) : Boolean = {
    if (from >= until)
      true
    else
      m.isDefinedAt(from) && defined_between(m, from + 1, until)
  }

  def smaller[T] (m : Map[BigInt, T], c : (T, T) => Int, from : BigInt, until : BigInt, x : T) : Boolean = {
    require(defined_between(m, from, until))
    if (from >= until) true
    else c(x, m(from)) <= 0 && smaller(m, c, from + 1, until, x)
  }

  def compare : (BigInt, BigInt) => Int = (x : BigInt, y : BigInt) => {
    if (x == y) 0
    else if (x < y) -1
    else 1
  }

  def lemma (m : Map[BigInt, BigInt], from : BigInt, until : BigInt, x : BigInt) : Boolean = {
    require(defined_between(m, from, until) && smaller(m, compare, from, until, x))
    if (from >= until)
      true
    else {
      check{defined_between(m, from + 1, until)} &&
      check{smaller(m, compare, from + 1, until, x)} &&
      check{lemma(m, from + 1, until, x)}
    }
  } holds // failed without --assumepre

  def smaller2 (m : Map[BigInt, BigInt], from : BigInt, until : BigInt, x : BigInt) : Boolean = {
    require(defined_between(m, from, until))
    if (from >= until) true
    else compare(x, m(from)) <= 0 && smaller2(m, from + 1, until, x)
  }

  def lemma2 (m : Map[BigInt, BigInt], from : BigInt, until : BigInt, x : BigInt) : Boolean = {
    require(defined_between(m, from, until) && smaller2(m, from, until, x))
    if (from >= until)
      true
    else {
      check{defined_between(m, from + 1, until)} &&
      check{smaller2(m, from + 1, until, x)} &&
      check{lemma2(m, from + 1, until, x)}
    }
  } holds // passed

}
