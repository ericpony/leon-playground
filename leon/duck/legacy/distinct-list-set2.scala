package duck.collection

import duck.proof.DistinctOps._
import leon.lang._
import leon.annotation._

object ListSet {

  implicit def ListToListSet[V] (list: List[V]): DistinctListOps[V] = {
    //require(distinct(list))
    //DistinctListOps(list)
    DistinctListOps(mk_distinct(list))
  }

  def mk_distinct[V] (list: List[V]): List[V] = (list match {
    case Nil()  => list
    case h :: t => if (t.contains(h)) mk_distinct(t) else h :: mk_distinct(t)
  }) ensuring { res =>
    if (distinct(list))
      res == list
    else {
      distinct(res) &&
        res.content == list.content &&
        res.size < list.size
    }
  }

  case class DistinctListOps[V] (list: List[V]) {

    def insert (e: V): List[V] = {
      require(distinct(list))
      if (list.isEmpty) e :: Nil[V]()
      else if (list.head == e) list
      else list.head :: list.tail.insert(e)
    } ensuring { res =>
      if (list.contains(e))
        res == list
      else {
        distinct(res) &&
          res.size == list.size + 1 &&
          res.content == list.content ++ Set(e)
      }
    }

    def remove (e: V): List[V] = {
      require(distinct(list))
      if (list.isEmpty) list
      else if (list.head == e) list.tail
      else list.head :: list.tail.remove(e)
    } ensuring { res =>
      if (!list.contains(e))
        res == list
      else {
        distinct(res) &&
          res.content ++ Set(e) == list.content &&
          res.size + 1 == list.size
      }
    }

    /**
     * Note: `other` doesn't have to be distinct
     */
    @induct
    def merge (other: List[V]): List[V] = {
      require(distinct(list))
      //    other match {
      //      case Nil()      => s
      //      case Cons(h, other) => union(insert(s, h), other)
      //    }
      other.foldRight(list)((e, tt) => tt.insert(e))
    } ensuring { res =>
      distinct(res) &&
        res.content == list.content ++ other.content &&
        //res.size == list.size + other.size - (list & other).size
        res.size <= list.size + other.size
    }
  }

}