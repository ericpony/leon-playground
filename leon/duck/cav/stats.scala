package duck.cav

import leon.lang._
import leon.annotation._

import scala.language.postfixOps


object Statistics {

  def min (x : BigInt, y : BigInt) = if (x < y) x else y
  def max (x : BigInt, y : BigInt) = if (x > y) x else y
  def corr[BigInt] (s1 : (BigInt, BigInt, BigInt, BigInt), s2 : (BigInt, BigInt, BigInt, BigInt)) = s1 == s2

  def comb_assoc_lemma (s1 : (BigInt, BigInt, BigInt, BigInt), s2 : (BigInt, BigInt, BigInt, BigInt), s3 : (BigInt, BigInt, BigInt, BigInt)) = {
    corr(comb(s1, comb(s2, s3)), comb(comb(s1, s2), s3))
  } holds

  def comb_comm_lemma (s1 : (BigInt, BigInt, BigInt, BigInt), s2 : (BigInt, BigInt, BigInt, BigInt)) = {
    corr(comb(s1, s2), comb(s2, s1))
  } holds

  def comb (s1 : (BigInt, BigInt, BigInt, BigInt), s2 : (BigInt, BigInt, BigInt, BigInt)) : (BigInt, BigInt, BigInt, BigInt) =
    (s1._1 + s2._1, s1._2 + s2._2, min(s1._3, s2._3), max(s1._4, s2._4))
}