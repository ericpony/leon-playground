
import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

import duck.proof.sugar._
import duck.collection._

object ImpliesBad {

  def bad (l : List[BigInt]) : List[BigInt] = {
    l match {
      case Nil() => Nil[BigInt]()
      case Cons(hd, tl) => Cons[BigInt](0, Cons[BigInt](hd, tl))
    }
  } ensuring { res =>
    (res != Nil[BigInt]()) implies (res.head == 0)
  }

}
