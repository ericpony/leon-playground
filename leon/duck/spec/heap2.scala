import duck.proof.sugar._
import duck.proof.MinOps._
import leon.lang._
import leon.annotation._
import leon.proof._
import HeapOps._
import scala.language.postfixOps

/**
 * REMARK: We may need a stronger definition of heap equivalence.
 */
object HeapSpec0 {
  def insert_commu_lemma (h: Heap, p1: BigInt, p2: BigInt): Boolean = {
    heapContent(insert(p2, insert(p1, h))) == heapContent(insert(p1, insert(p2, h)))
  } holds /* verified by Leon */

  def merge_commu_lemma (h1: Heap, h2: Heap): Boolean = {
    heapContent(merge(h1, h2)) == heapContent(merge(h2, h1))
  } holds /* verified by Leon */

  def merge_assoc_lemma (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    heapContent(merge(h1, merge(h2, h3))) == heapContent(merge(merge(h1, h2), h3))
  } holds /* verified by Leon */
}

@ignore
object HeapSpec1 {

  def bounded_eq (h1: Heap, h2: Heap, bound: BigInt): Boolean = {
    if (bound <= 0) true
    else if (h1 == h2) true
    else findMin(h1) == findMin(h2) &&
      bounded_eq(deleteMin(h1), deleteMin(h2), bound - 1)
  }

  def sorted_eq (h1: Heap, h2: Heap, bound: BigInt): Boolean = {
    require(heapContent(h1) == heapContent(h2))
    bounded_eq(h1, h2, bound)
  } holds /* timeout */

  def insert_commu_lemma (h: Heap, p1: BigInt, p2: BigInt, bound: BigInt): Boolean = {
    val H1 = insert(p2, insert(p1, h))
    val H2 = insert(p1, insert(p2, h))
    bounded_eq(H1, H2, bound) because {
      findMin(H1) == findMin(H2) &&
        check {
          findMin(insert(p2, insert(p1, deleteMin(h)))) ==
            findMin(insert(p1, insert(p2, deleteMin(h))))
        } &&
        check { insert_commu_lemma(deleteMin(h), p1, p2, bound - 1) }
    }
  } holds /* timeout */
}

object HeapOps {

  sealed abstract class Heap

  private case class Node (rank: BigInt, elem: BigInt, nodes: Heap)

  private case class Nodes (head: Node, tail: Heap) extends Heap

  case object Empty extends Heap

  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Abstraction functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  def heapContent (h: Heap): Set[BigInt] = h match {
    case Empty        => Set.empty[BigInt]
    case Nodes(n, ns) => nodeContent(n) ++ heapContent(ns)
  }

  def nodeContent (n: Node): Set[BigInt] = n match {
    case Node(_, e, h) => Set(e) ++ heapContent(h)
  }

  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Helper/local functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  private def reverse (h: Heap): Heap = reverse0(h, Empty)

  private def reverse0 (h: Heap, acc: Heap): Heap = (h match {
    case Empty        => acc
    case Nodes(n, ns) => reverse0(ns, Nodes(n, acc))
  }) ensuring (res => heapContent(res) == heapContent(h) ++ heapContent(acc))

  private def link (t1: Node, t2: Node) = (t1, t2) match {
    case (Node(r, e1, ns1), Node(_, e2, ns2)) =>
      if (e1 <= e2) {
        Node(r + 1, e1, Nodes(t2, ns1))
      } else {
        Node(r + 1, e2, Nodes(t1, ns2))
      }
  }

  private def insertNode (t: Node, h: Heap): Heap = (h match {
    case Empty         => Nodes(t, Empty)
    case Nodes(t2, h2) =>
      if (t.rank < t2.rank) {
        Nodes(t, h)
      } else {
        insertNode(link(t, t2), h2)
      }
  }) ensuring { res =>
    heapContent(res) == nodeContent(t) ++ heapContent(h) && {
      val Node(_, v, _) = t
      findMin(res).get == min(v, findMin(h).getOrElse(v))
    }
  }

  private def getMin (h: Heap): (Node, Heap) = {
    require(h != Empty)
    (h: @unchecked) match {
      case Nodes(t, Empty) => (t, Empty)
      case Nodes(t, ts)    =>
        val (t0, ts0) = getMin(ts)
        if (t.elem < t0.elem) {
          (t, ts)
        } else {
          (t0, Nodes(t, ts0))
        }
    }
  } ensuring (_ match {
    case (n, h2) => nodeContent(n) ++ heapContent(h2) == heapContent(h) &&
      n.elem == findMin(h).get &&
      n.elem <= findMin(h2).getOrElse(n.elem) &&
      findMin(h).get <= findMin(h2).getOrElse(n.elem) &&
      findMin(h).get <= findMin(reverse(n.nodes)).getOrElse(n.elem)
    //min(getMin(h2)._1.elem, getMin(h))
  })

  /*~~~~~~~~~~~~~~~~*/
  /* Heap interface */
  /*~~~~~~~~~~~~~~~~*/
  def empty (): Heap = {
    Empty
  } ensuring (res => heapContent(res) == Set.empty[BigInt])

  def isEmpty (h: Heap): Boolean = {
    (h == Empty)
  } ensuring (res => res == (heapContent(h) == Set.empty[BigInt]))

  def insert (e: BigInt, h: Heap): Heap = {
    insertNode(Node(0, e, Empty), h)
  } ensuring { res =>
    heapContent(res) == heapContent(h) ++ Set(e) &&
      findMin(res).get == min(e, findMin(h).getOrElse(e))
  }

  /* NOTE: needs ~10 seconds to be verified */
  def merge (h1: Heap, h2: Heap): Heap = ((h1, h2) match {
    case (_, Empty)                       => h1
    case (Empty, _)                       => h2
    case (Nodes(t1, ts1), Nodes(t2, ts2)) =>
      if (t1.rank < t2.rank) {
        Nodes(t1, merge(ts1, h2))
      } else if (t2.rank < t1.rank) {
        Nodes(t2, merge(h1, ts2))
      } else {
        insertNode(link(t1, t2), merge(ts1, ts2))
      }
  }) ensuring { res =>
    heapContent(res) == heapContent(h1) ++ heapContent(h2) && {
      res != Empty implies {
        val v = findMin(res).get
        v == min(findMin(h1).getOrElse(v), findMin(h2).getOrElse(v))
      }
    }
  }

  def findMin (h: Heap): Option[BigInt] = {
    h match {
      case Empty                    => None[BigInt]()
      case Nodes(Node(_, e, _), ns) =>
        findMin(ns) match {
          case None()   => Some(e)
          case Some(e2) => Some(min(e, e2))
        }
    }
  } ensuring { res =>
    res match {
      case None()  => isEmpty(h)
      case Some(v) => heapContent(h).contains(v)
    }
  }

  @induct
  def deleteMin (h: Heap): Heap = (h match {
    case Empty     => Empty
    case ts: Nodes =>
      val (Node(_, _, ns1), ns2) = getMin(ts)
      merge(reverse(ns1), ns2)
  }) ensuring { res =>
    heapContent(res).subsetOf(heapContent(h)) && {
      h != Empty implies heapContent(res) ++ Set(findMin(h).get) == heapContent(h)
    } && {
      res != Empty implies findMin(h).get <= findMin(res).get
    }
  }
}

@ignore
object HeapTest {
  def sanity0 (): Boolean = {
    val h0: Heap = Empty
    val h1 = insert(BigInt(42), h0)
    val h2 = insert(BigInt(72), h1)
    val h3 = insert(BigInt(0), h2)
    findMin(h0) == None[BigInt]() &&
      findMin(h1) == Some(BigInt(42)) &&
      findMin(h2) == Some(BigInt(42)) &&
      findMin(h3) == Some(BigInt(0))
  }.holds

  def sanity1 (): Boolean = {
    val h0 = insert(BigInt(42), Empty)
    val h1 = insert(BigInt(0), Empty)
    val h2 = merge(h0, h1)
    findMin(h2) == Some(BigInt(0))
  }.holds

  def sanity3 (): Boolean = {
    val h0 = insert(BigInt(42), insert(BigInt(0), insert(BigInt(12), Empty)))
    val h1 = deleteMin(h0)
    findMin(h1) == Some(BigInt(12))
  }.holds
}