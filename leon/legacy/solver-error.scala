package duck.spec

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.implicitConversions

object AAA {

  def lemma (x : BigInt, y : BigInt, z : BigInt) : Boolean = {
    require(x == y && y == z)
    x == z because {
      x ==| trivial |
      y ==| trivial |
      z
    }.qed
  }.holds 

}
