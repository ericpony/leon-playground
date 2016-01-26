package duck.cav

import duck.collection._
import duck.proof.MinOps._
import duck.proof.PermutationOps._
import duck.spec.DistinctListOps._

import leon.lang._
import leon.annotation._

import scala.language.postfixOps


object SetAggregation {

  def ~[V] (m1 : List[V], m2 : List[V]) = permutation(m1, m2)

  def corr[V] (m1 : (V, List[V]), m2 : (V, List[V])) =
    m1._1 == m2._1 && m1._2 ~ m2._2

  def insert_invariant[V] (l1 : List[V], l2 : List[V], e : V) : Boolean = {
    require(distinct(l1) && distinct(l2) && l1 ~ l2)
    val L1 = insert(l1, e)
    val L2 = insert(l2, e)
    distinct(L1) && distinct(L2) && L1 ~ L2
  } holds /* verified */

  def union_invariant[V] (l1 : List[V], l2 : List[V], l3 : List[V], l4 : List[V]) = {
    require(l1 ~ l2 && l3 ~ l4)
    union(l1, l3) ~ union(l2, l4)
  } holds /* timeout */

  def comb_assoc_lemma (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt]), m3 : (BigInt, List[BigInt])) = {
    require(distinct(m1._2) && distinct(m2._2) && distinct(m3._2))
    corr(comb(m1, comb(m2, m3)), comb(comb(m1, m2), m3))
  } holds /* timeout */

  def comb_comm_lemma (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt])) = {
    require(distinct(m1._2) && distinct(m2._2))
    corr(comb(m1, m2), comb(m2, m1)) // because union_comm(m1._2, m2._2)
  } holds /* timeout */

  def comb (m1 : (BigInt, List[BigInt]), m2 : (BigInt, List[BigInt])) : (BigInt, List[BigInt]) = {
    require(distinct(m1._2) && distinct(m2._2))
    (min(m1._1, m2._1), union(m1._2, m2._2))
  } ensuring {
    res => distinct(res._2) //&& res._1 == min(res._2)
  }
}