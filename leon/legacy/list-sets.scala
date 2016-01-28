
import duck.cav
import leon.lang._
import leon.annotation._
import scala.language.implicitConversions
import leon.proof._

import duck.collection._
import duck.spec._
import duck.proof.DistinctOps._
import duck.proof.DistinctLemmas._

object ListSet0Ops {
  def mk_set[T] : List[T] = Nil()
  def insert[T] (e : T, set : List[T]) : List[T] = 
    (set match {
      case Nil ()      => Cons (e, Nil ())
      case Cons (h, t) => if (e == h) set else Cons (h, insert (e, t))
    }) ensuring (res => res.content == set.content ++ Set (e))
  def insertAll[T] (elts : List[T], set : List[T]) : List[T] =
    elts.foldRight (set) (insert)
  def union[T] (set : List[T], tes : List[T]) : List[T] =
    insertAll (set, tes)
}

object ListSet0Lemmas {
  // type checker has established bisimulation
}

object ListSetMOps {
  def mk_set[T] : List[T] = ListSet0Ops.mk_set
  def is_member[T] (e : T, set : List[T]) : Boolean =
    (set match {
      case Nil ()      => false
      case Cons (h, t) => (h == e) || is_member (e, t)
    }) ensuring (res => res == set.contains (e))

  def insert[T] (e : T, set : List[T]) : List[T] = 
    ListSet0Ops.insert (e : T, set : List[T])
  def insertAll[T] (elts : List[T], set : List[T]) : List[T] =
    (ListSet0Ops.insertAll (elts, set)) ensuring {
      res => res.content == elts.content ++ set.content because
          ListSetMLemmas.insertAll_content (elts, set)
    }
  def union[T] (set : List[T], tes : List[T]) : List[T] =
    (ListSet0Ops.union (set, tes)) ensuring {
      res => res.content == set.content ++ tes.content because
        ListSetMLemmas.insertAll_content (set, tes)
    }
}

object ListSetMLemmas {
  def check_is_member[T] (e : T, s : List[T], t : List[T]) : Boolean = {
    require (s.content == t.content)
    ListSetMOps.is_member (e, s) == ListSetMOps.is_member (e, t)
  }.holds

  def check_insert[T] (e : T, s : List[T], t : List[T]) : Boolean = {
    require (s.content == t.content)
    ListSetMOps.insert (e, s).content == ListSetMOps.insert (e, t).content
  }.holds

  @induct
  def check_insertAll[T] (es : List[T], s : List[T], t : List[T]) : Boolean = {
    require (s.content == t.content)
    ListSetMOps.insertAll (es, s).content == ListSetMOps.insertAll (es, t).content
  }.holds

  @induct
  def insertAll_content[T] (elts : List[T], s : List[T]) : Boolean = {
    ListSetMOps.insertAll (elts, s).content == elts.content ++ s.content
  }.holds

  @induct
  def check_union[T] (s0 : List[T], s1 : List[T], t0 : List[T], t1 : List[T]) : Boolean = {
    require (s0.content == s1.content && t0.content == t1.content)
    ListSetMOps.union (s0, t0).content == ListSetMOps.union (s1, t1).content
  }.holds
}

object ListSetOps {
  def mk_set[T] : List[T] = ListSetMOps.mk_set
  def is_member[T] (e : T, set : List[T]) : Boolean =
    (set match {
      case Nil ()      => false
      case Cons (h, t) => (h == e) || is_member (e, t)
    }) ensuring { res => res == set.contains (e) }
  def insert[T] (e : T, set : List[T]) : List[T] =
    ListSetMOps.insert (e, set)
  def remove[T] (e : T, set : List[T]) : List[T] = {
    require (distinct (set))
    set match {
      case Nil ()      => set
      case Cons (h, t) => if (e == h) t else Cons (h, remove (e, t))
    }
  } ensuring { res => res.content == set.content -- Set (e) }
  def insertAll[T] (elts : List[T], set : List[T]) : List[T] =
    ListSetMOps.insertAll (elts, set)
  def union[T] (set : List[T], tes : List[T]) : List[T] =
    ListSetMOps.union (set, tes)
}

object ListSetLemmas {
  @induct
  def check_is_member[T] (e : T, s : List[T], t : List[T]) : Boolean = {
    require (distinct (s) && distinct (t) && s.content == t.content)
    cav.ListSetOps.is_member (e, s) == cav.ListSetOps.is_member (e, t)
  }.holds

  @induct
  def insert_distinct[T] (e : T, set : List[T]) : Boolean = {
    require (distinct (set))
    distinct (cav.ListSetOps.insert (e, set))
  }.holds

  def check_insert[T] (e : T, s : List[T], t : List[T]) : Boolean = {
    require (distinct (s) && distinct (t) && s.content == t.content)
    val u = cav.ListSetOps.insert (e, s)
    val v = cav.ListSetOps.insert (e, t)
    distinct (u) && distinct (v) && u.content == v.content because
      insert_distinct (e, s) && insert_distinct (e, t)
  }.holds

  @induct
  def remove_distinct[T] (e : T, set : List[T]) : Boolean = {
    require (distinct (set))
    distinct (cav.ListSetOps.remove (e, set))
  }.holds

  def check_remove[T] (e : T, s : List[T], t : List[T]) : Boolean = {
    require (distinct (s) && distinct (t) && s.content == t.content)
    val u = cav.ListSetOps.remove (e, s)
    val v = cav.ListSetOps.remove (e, t)
    distinct (u) && distinct (v) && u.content == v.content because
      remove_distinct (e, s) && remove_distinct (e, t)
  }.holds

  @induct
  def insertAll_distinct[T] (es : List[T], set : List[T]) : Boolean = {
    require (distinct (set))
    if (es.isEmpty) {
      distinct (cav.ListSetOps.insertAll (es, set))
    } else {
      distinct (cav.ListSetOps.insertAll (es, set)) because {
        distinct (cav.ListSetOps.insertAll (es.tail, set)) &&
        insert_distinct (es.head, cav.ListSetOps.insertAll (es.tail, set))
      }
    }
  }.holds

  def check_insertAll[T] (es : List[T], s : List[T], t : List[T]) : Boolean = {
    require (distinct (s) && distinct (t) && s.content == t.content)
    val u = cav.ListSetOps.insertAll (es, s)
    val v = cav.ListSetOps.insertAll (es, t)
    distinct (u) && distinct (v) && u.content == v.content because
      insertAll_distinct (es, s) && insertAll_distinct (es, t)
  }.holds

  def check_union[T] (s0 : List[T], s1 : List[T], t0 : List[T], t1 : List[T]) : Boolean = {
    require (distinct (s0) && distinct (s1) && s0.content == s1.content && 
             distinct (t0) && distinct (t1) && t0.content == t1.content)
    val u0 = cav.ListSetOps.union (s0, t0)
    val u1 = cav.ListSetOps.union (s1, t1)
    distinct (u0) && distinct (u1) && u0.content == u1.content because
      check_insertAll (s0, t0, t1) && check_insertAll (s1, t0, t1)
  }.holds
}

