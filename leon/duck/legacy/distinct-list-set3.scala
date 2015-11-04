import duck.proof.DistinctOps._
import duck.proof.PermutationSpec._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.DeleteOps._
import duck.collection._
import leon.annotation._
import leon.lang._
import leon.proof._
import DistinctList._
import scala.language.postfixOps

object DistinctList {

  implicit def ListToListSet[V] (list: List[V]): DistinctListOps[V] = {
    DistinctListOps(list)
    //DistinctListOps(mk_distinct(list))
  }

  def mk_distinct[V] (list: List[V]): List[V] = {
    list match {
      case Nil()  => list
      case h :: t =>
        if (t.contains(h))
          mk_distinct(t)
        else
          h :: mk_distinct(t)
    }
  } ensuring { res =>
    distinct(res) &&
      (if (distinct(list))
        res == list
      else {
        res.content == list.content &&
          res.size < list.size
      })
  }

  @library
  case class DistinctListOps[V] (list: List[V]) {

    //    def insert (e: V): List[V] = {
    //      require(distinct(list))
    //      if (list.isEmpty) e :: Nil[V]()
    //      else if (list.head == e) list
    //      else list.head :: list.tail.insert(e)
    //    } ensuring { res =>
    //      if (list.contains(e))
    //        res == list
    //      else {
    //        distinct(res) &&
    //          res == list ++ Cons(e, Nil[V]())
    //      }
    //    }

    def insert (e: V): List[V] = {
      require(distinct(list))
      if (list.contains(e))
        list
      else
        e :: list
    } ensuring { res =>
      if (list.contains(e))
        res == list
      else
        distinct(res) && res == e :: list
    }

    def remove (e: V): List[V] = {
      require(distinct(list))
      if (list.isEmpty) list
      else if (list.head == e) list.tail
      else list.head :: list.tail.remove(e)
    } ensuring { res =>
      res == delete(list, e) &&
        distinct(res) &&
        (if (!list.contains(e))
          res == list
        else {
          res.content ++ Set(e) == list.content &&
            res.size + 1 == list.size
        })
    }

    @induct
    def merge (other: List[V]): List[V] = {
      require(distinct(list) && distinct(other))
      // We prefer keeping elements in `list` when
      // there are duplicate elements. This design
      // choice makes it easier to prove lemmas
      // involving merges.
      //      list match {
      //        case Nil()  => other
      //        case h :: t =>
      //          if (other.contains(h))
      //            list.merge(other.remove(h))
      //          else
      //            h :: (t.merge(other))
      //      }
      mk_distinct(list ++ other)
    } ensuring { res =>
      distinct(res) &&
        permutation(res, other.merge(list)) &&
        res.content == list.content ++ other.content &&
        // res.size == list.size + other.size - (list & other).size &&
        res.size <= list.size + other.size
    }
  }

}

object DistinctListLemmas {

  @induct
  def insert_comm_permutation[V] (list: List[V], e: V, f: V): Boolean = {
    require(distinct(list))
    permutation(list.insert(e).insert(f), list.insert(f).insert(e)) because {
      if (list contains e)
        permutation_refl(list.insert(f))
      else if (list contains f)
        permutation_refl(list.insert(e))
      else
        trivial
    }
  } holds /* verified */

  def insert_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(permutation(s, t) && distinct(s) && distinct(t))
    permutation(s.insert(e), t.insert(e)) because {
      if (s contains e)
        trivial
      else
        permutation_append(s, t, Cons(e, Nil[V]))
    }
  } holds /* verified */

  @induct
  def remove_delete[V] (list: List[V], e: V): Boolean = {
    require(distinct(list) && list.contains(e))
    list.remove(e) == delete(list, e)
  } holds /* verified */

  def remove_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(permutation(s, t) && distinct(s) && distinct(t))
    permutation(s.remove(e), t.remove(e)) because {
      if (s contains e) {
        permutation_delete(s, t, e) &&
          remove_delete(s, e) &&
          remove_delete(t, e)
      } else
        trivial
    }
  } holds /* timeout */

  def merge_permutation[V] (s: List[V], t: List[V], u: List[V], v: List[V]): Boolean = {
    require(permutation(s, u) && permutation(t, v) &&
      distinct(s) && distinct(t) && distinct(u) && distinct(v))
    permutation(s.merge(t), u.merge(v)) because {
      if (s.isEmpty)
        trivial
      else {
        distinct(s.tail.merge(t)) &&
          distinct(u.remove(s.head).merge(v)) &&
          permutation(s.tail, u.remove(s.head)) &&
          merge_permutation(s.tail, t, u.remove(s.head), v) &&
          permutation(s.tail.merge(t), u.remove(s.head).merge(v)) &&
          insert_permutation(
            s.tail.merge(t),
            u.remove(s.head).merge(v),
            s.head) &&
          permutation(
            s.tail.merge(t).insert(s.head),
            u.remove(s.head).merge(v).insert(s.head)
          ) because {
          merge_permutation(s.tail, t, u.remove(s.head), v) &&
            permutation(s.tail.merge(t), u.remove(s.head).merge(v)) &&
            insert_permutation(s.tail.merge(t), u.remove(s.head).merge(v), s.head)
        } &&
          merge_permutation_2(s, u, v) &&
          permutation_tran(
            s.tail.merge(t).insert(s.head),
            u.remove(s.head).merge(v).insert(s.head),
            u.merge(v)) &&
          // permutation(s.merge(t), s.tail.merge(t).insert(s.head)) because {
          permutation_refl(s) &&
          merge_permutation_2(s, s, t) && // }
          permutation_tran(s.merge(t), s.tail.merge(t).insert(s.head), u.merge(v)) &&
          permutation(s.merge(t), u.merge(v))
      }
    }
  } holds /* verified */

  def merge_permutation_2[V] (s: List[V], u: List[V], t: List[V]): Boolean = {
    require(permutation(s, u) && s != Nil[V]() &&
      distinct(s) && distinct(t) && distinct(u))
    permutation(
      u.remove(s.head).merge(t).insert(s.head),
      u.merge(t)
    ) because
      merge_insert_delete_permutation(u, t, s.head)
  } holds /* verified */

  def merge_insert_delete_permutation[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(s.contains(e) && distinct(s) && distinct(t))
    permutation(
      s.remove(e).merge(t).insert(e),
      s.merge(t)
    ) because {
      if (s.head == e) {
        check { merge_insert_delete_permutation_2(s, t) } &&
          check { permutation(s.remove(e).merge(t).insert(e), s.merge(t)) }
      } else {
        // permutation(
        // s.tail.remove(e).merge(t).insert(e),
        // s.tail.merge(t)) because
        check { merge_insert_delete_permutation_3(s, t, e) } &&
          check {
            insert_permutation(
              s.tail.remove(e).merge(t).insert(e),
              s.tail.merge(t), s.head)
          } && {
          if (t.contains(s.head)) {
            check { s.tail.remove(e).merge(t).insert(e).insert(s.head) == s.tail.remove(e).merge(t).insert(e) } &&
              check { s.remove(e) == s.tail.remove(e).insert(s.head) }
          } else {
            check { s.remove(e).merge(t).insert(e) == s.tail.remove(e).merge(t).insert(e).insert(s.head) } &&
              check { s.merge(t) == s.tail.merge(t).insert(s.head) } &&
              check { permutation(s.remove(e).merge(t).insert(e), s.merge(t)) }
          }
        }
        //          check {
        //            insert_comm_permutation(
        //              s.tail.remove(e).merge(t),
        //              s.head, e)
        //          } &&
        //          check {
        //            permutation_tran(
        //              s.tail.remove(e).merge(t).insert(s.head).insert(e),
        //              s.tail.remove(e).merge(t).insert(e).insert(s.head),
        //              s.tail.merge(t).insert(s.head))
        //          } &&
        //          check {
        //            permutation(s.tail.merge(t).insert(s.head), mk_distinct(s.head :: (s.tail.merge(t)))) because
        //              insert_cons_permutation(s.tail.merge(t), s.head)
        //          } //&&
        //          check {} &&
        //          check {} &&
        //          check { permutation(s.remove(e).merge(t).insert(e), s.merge(t)) }
      }
    }
  } holds /* timeout */

  @induct
  def test[V] (t: List[V], s: List[V], e: V): Boolean = {
    require(s.contains(e) && distinct(s) && distinct(t) && t.contains(e))
    check { permutation(s.tail.merge(t), s.merge(t))
    }
  } holds

  @induct
  def test2[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(s.contains(e) && distinct(s) && distinct(t) && s.head != e && t.contains(s.head))
    check { s.tail.remove(e).merge(t).insert(s.head) == s.tail.remove(e).merge(t) } &&
      check { permutation(s.merge(t), s.tail.merge(t)) }
  } holds

  def merge_insert_delete_permutation_4[V] (s: List[V], t: List[V]): Boolean = {
    require(s != Nil[V]() && distinct(s) && distinct(t))
    permutation(mk_distinct(s.head :: (s.tail.merge(t))), mk_distinct(s.merge(t))) because {
      if (t.contains(s.head)) {
        check { mk_distinct(s.head :: (s.tail.merge(t))) == mk_distinct(s.tail.merge(t)) } &&
          check { mk_distinct(s.head :: (s.tail.merge(t))) == mk_distinct(s.tail.merge(t)) } &&
          check { permutation_eq(mk_distinct(s.head :: (s.tail.merge(t))), mk_distinct(s.merge(t))) }
      } else {
        true
        //         check { permutation_delete_cons()}
      }
    }
  } holds

  def insert_cons_permutation[V] (l: List[V], e: V): Boolean = {
    require(distinct(l))
    permutation(l.insert(e), mk_distinct(e :: l)) because {
      permutation_eq(l.insert(e), mk_distinct(e :: l))
    }
  } holds

  def merge_insert_delete_permutation_2[V] (s: List[V], t: List[V]): Boolean = {
    require(s != Nil[V]() && distinct(s) && distinct(t))
    permutation(
      s.tail.merge(t).insert(s.head),
      s.merge(t)
    ) because {
      s.tail.merge(t).insert(s.head) == s.merge(t) &&
        permutation_eq(s.tail.merge(t).insert(s.head), s.merge(t))
    }
  } holds /* timeout */

  def merge_insert_delete_permutation_3[V] (s: List[V], t: List[V], e: V): Boolean = {
    require(s != Nil[V]() && s.tail.contains(e) && distinct(s) && distinct(t))
    permutation(
      s.tail.remove(e).merge(t).insert(e),
      s.tail.merge(t)
    ) because
      merge_insert_delete_permutation(s.tail, t, e)
  } holds /* timeout */

  @induct
  def permutation_first_last_swap[V] (l: List[V], e: V) = {
    permutation(e :: l, l ++ Cons(e, Nil[V]()))
  } holds
}
