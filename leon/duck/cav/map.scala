package duck.cav

import duck.collection.KList._
import duck.collection._
import duck.spec.DistinctListOps._
import duck.proof.KListLemmas._

import leon.lang._
import leon.proof._
import leon.annotation._

import scala.language.postfixOps


object Map {

  //def ~[K, V] (m1 : KList[K, V], m2 : KList[K, V]) = permutation(m1, m2)

  def isMap[K, V] (m : KList[K, V]) = distinct(m.keys)

  def update_invariant[K, V] (m1 : KList[K, V], m2 : KList[K, V], e : Item[K, V]) : Boolean = {
    require(m1 ~ m2 && isMap(m1) && isMap(m2))
    m1.update(e) ~ m2.update(e) because {
      if (!m1.hasKey(e.key) || !m2.hasKey(e.key))
        trivial
      else
        update_invariant(m1.delete(e.key), m2.delete(e.key), e)
    }
  } holds /* verified by Leon */

  def comb_invariant[K, V] (m1 : KList[K, V], m2 : KList[K, V], m3 : KList[K, V], m4 : KList[K, V]) = {
    require(m1 ~ m2 && m3 ~ m4 && isMap(m1) && isMap(m2) && isMap(m3) && isMap(m4))
    comb(m1, m3) ~ comb(m2, m4)
  } holds /* verified by Leon */

  @induct
  def merge_invariant[K, V] (m1 : KList[K, V], m2 : KList[K, V], m3 : KList[K, V], m4 : KList[K, V]) : Boolean = {
    require(m1 ~ m2 && m3 ~ m4 && isMap(m1) && isMap(m2) && isMap(m3) && isMap(m4))
    val M1 = merge(m1, m3)
    val M2 = merge(m2, m4)

    if (m1.isEmpty || m3.isEmpty)
      trivial
    else {
      M1 ~ M2 because {
        val h = m1.head
        val M11 = merge(delete(m1, h), delete(m3, h))
        val M21 = merge(delete(m2, h), delete(m4, h))
        check { M11 ~ M21 because merge_invariant(delete(m1, h), delete(m2, h), delete(m3, h), delete(m4, h)) } &&
          permutation_delete(m1, m2, h) &&
          permutation_delete(m3, m4, h) &&
          check {
            check { M1 ~ KCons(h, M11) } &&
              check { KCons(h, M21) ~ M2 } &&
              check { KCons(h, M11) ~ KCons(h, M21) } &&
              permutation_tran_lemma2(M1, KCons(h, M11), KCons(h, M21), M2)
          }
      }
    }
  } holds

  @induct
  def insert_comm_lemma[K, V] (m : KList[K, V], p1 : Item[K, V], p2 : Item[K, V]) = {
    require(p1.key != p2.key && isMap(m))
    m.update(p1).update(p2) ~ m.update(p2).update(p1)
  } holds /* verified by Leon */

  def comb_comm_lemma[K, V] (m1 : KList[K, V], m2 : KList[K, V]) = {
    require((m1.keys & m2.keys) == Nil[K]() && isMap(m1) && isMap(m2))
    comb(m1, m2) ~ comb(m2, m1)
  } holds /* verified by Leon */

  def comb_assoc_lemma[K, V] (m1 : KList[K, V], m2 : KList[K, V], m3 : KList[K, V]) = {
    require((m1.keys & m2.keys) == Nil[K]() &&
      (m2.keys & m3.keys) == Nil[K]() &&
      (m3.keys & m1.keys) == Nil[K]() &&
      isMap(m1) && isMap(m2) && isMap(m3))
    comb(m1, comb(m2, m3)) ~ comb(comb(m1, m2), m3)
  } holds /* verified by Leon */

  def comb[K, V] (m1 : KList[K, V], m2 : KList[K, V]) : KList[K, V] = m1 ++ m2

  def merge_comm_lemma[K, V] (m1 : KList[K, V], m2 : KList[K, V]) : Boolean = {
    require((m1.keys & m2.keys) == Nil[K]() && isMap(m1) && isMap(m2))
    val M1 = merge(m1, m2)
    val M2 = merge(m2, m1)
    M1 ~ M2 because {
      if (m1.isEmpty || m2.isEmpty)
        trivial
      else {
        val h = m1.head
        val M11 = merge(m1.tail, m2)
        val M21 = merge(m2, m1.tail)
        M11 ~ M21 because merge_comm_lemma(m1.tail, m2) &&
          M1 ~ KCons(h, M11) &&
          KCons(h, M21) ~ M2 &&
          KCons(h, M11) ~ KCons(h, M21) &&
          M1 ~ M2 because permutation_tran_lemma2(M1, KCons(h, M11), KCons(h, M21), M2)
      }
    }
  } holds /* verified by Leon */

  @induct
  def merge[K, V] (m1 : KList[K, V], m2 : KList[K, V]) : KList[K, V] = {
    require(isMap(m1) && isMap(m2))
    if (m2.isEmpty) m1
    else if (m1.isEmpty) m2
    else {
      val KCons(hd, tl) = m1
      // keys in m1 overwrite keys in m2
      merge(tl, m2.update(hd))
    }
  } ensuring { res => isMap(res) }

}