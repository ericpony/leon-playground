
import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

import duck.collection._

object ImpliesGood {

  def good (l : List[BigInt]) : List[BigInt] = {
    l match {
      case Nil() => Nil[BigInt]()
      case Cons(hd, tl) => Cons[BigInt](0, Cons[BigInt](hd, tl))
    }
  } ensuring { res =>
    ((res != Nil[BigInt]()) ==> (res.head == 0))
  }

}
