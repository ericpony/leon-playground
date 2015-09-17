import leon.annotation.{ignore, induct}
import leon.collection._
import leon.lang._
import leon.proof._
import DeleteSpec._
import DeleteOps._
import DeleteLemmas._
import scala.language.postfixOps

object DeleteSpec {
  @induct
  def delete_comm[V] (list: List[V], a: V, b: V): Boolean = {
    delete(delete(list, a), b) == delete(delete(list, b), a)
  } holds

  @induct
  def delete_concat[V] (l1: List[V], l2: List[V], e: V): Boolean = {
    require(l1 contains e)
    delete(l1, e) ++ l2 == delete(l1 ++ l2, e)
  } holds

  @induct
  def delete_content[V] (list: List[V], e: V): Boolean = {
    require(list.contains(e))
    list.content == delete(list, e).content ++ Set(e)
  } holds

  @induct
  def delete_not_contains[V] (list: List[V], m: V): Boolean = {
    require(!list.contains(m))
    delete(list, m) == list
  } holds

  @induct
  def delete_contains[V] (list: List[V], a: V, b: V) = {
    require(list.contains(a) && a != b)
    delete(list, b).contains(a)
  } holds
}

object DeleteOps {
  /**
   * Remove an element from a list.
   * @param list a list
   * @param e an element
   * @return a list obtained by removing e from the input list
   */
  def delete[V] (list: List[V], e: V): List[V] = {
    if (list == Nil[V]()) list
    else if (list.head == e) list.tail
    else Cons(list.head, delete(list.tail, e))
  } ensuring { res =>
    res.size == (if (list contains e) list.size - 1 else list.size) &&
      res.content.subsetOf(list.content)
  }
}

object DeleteLemmas {
  @induct
  def delete_concat_lemma1[V] (l1: List[V], l2: List[V], m: V): Boolean = {
    require(!l1.contains(m))
    l1 ++ delete(l2, m) == delete(l1 ++ l2, m)
  } holds /* verified by leon */

  def delete_concat_lemma2[V] (l1: List[V], l2: List[V], m: V): Boolean = {
    require(!l2.contains(m))
    delete(l1, m) ++ l2 == delete(l1 ++ l2, m) because {
      l1 match {
        case Nil()      => delete_not_contains(l2, m)
        case Cons(h, t) => delete_concat_lemma2(t, l2, m)
      }
    }
  } holds /* verified by leon */

  @induct
  def delete_content[V] (list: List[V], e: V): Boolean = {
    require(list.contains(e))
    list.content == delete(list, e).content ++ Set(e)
  } holds
}