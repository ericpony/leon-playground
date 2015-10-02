package duck.collection

import duck.proof.sugar._
import duck.proof.DistinctListSetLemmas._
import leon.proof._
import leon.lang._
import leon.annotation._

package object DistinctListSetOps {
  def insert[V] (set: List[V], e: V): List[V] = {
    if (set.isEmpty) Cons(e, Nil[V])
    else if (set.head == e) set
    else set.head :: insert(set.tail, e)
  } ensuring {
    res => res.content == set.content ++ Set(e) &&
      res.size <= set.size + 1
  }

  def remove[V] (set: List[V], e: V): List[V] = {
    if (set.isEmpty) set
    else if (set.head == e) set.tail
    else set.head :: remove(set.tail, e)
  } ensuring {
    res => res.content.subsetOf(set.content) &&
      res.size <= set.size
  }

  def union[V] (s: List[V], t: List[V]): List[V] = {
    //    t match {
    //      case Nil()      => s
    //      case Cons(h, t) => union(insert(s, h), t)
    //    }
    s.foldRight(t)((e, tt) => insert(tt, e))
  } ensuring {
    res => res == union(t, s) &&
      res.content == s.content ++ t.content &&
      res.size == s.size + t.size - (s & t).size
  }
}
