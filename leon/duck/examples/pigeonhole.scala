package duck.examples

import leon.lang._
import scala.language.postfixOps
import scala.language.implicitConversions

object PigeonHolePrinciples {

  def exists[A] (p : A => Boolean) : Boolean = !forall((x : A) => !p(x))

  def exists[A, B] (p : (A, B) => Boolean) : Boolean = !forall((x : A, y : B) => !p(x, y))

  def inbound[T] (i : Int, a : Array[T]) = 0 <= i && i < a.length

  def btw (i : Int, lower : Int, upper : Int) = lower <= i && i <= upper;

  def pigeon_1 (a : Array[Int], m : Int) : Boolean = {
    require(btw(m, 2, a.length) &&
      forall((i : Int) => inbound(i, a) ==> btw(a(i), 0, m)))
    exists((i : Int, j : Int) => (inbound(i, a) && inbound(j, a) && i != j) ==> (a(i) == a(j)))
  } holds
}
