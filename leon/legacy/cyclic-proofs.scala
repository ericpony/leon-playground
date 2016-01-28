import leon.lang._
import leon.proof._

object Examples {
  // Type I
  def foo: Boolean = {
    1 == 2 because foo
  }.holds
  
  // Type II
  def hoo(a: Int, b: Int): Int = {
    a
  } ensuring {
    res => b == hoo(b, a)
  }

  // Type III
  def goo: Int = {
    1
  } ensuring {
    res => res == 2 because goo_lemma
  }
  def goo_lemma = {
    goo == 2
  }.holds
  
}