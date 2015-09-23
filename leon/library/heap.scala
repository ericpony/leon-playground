import duck.sugar._
import leon.lang._
import leon.annotation._
import leon.proof._
import LeftistHeapOps._
import scala.language.postfixOps

/**
 * REMARK: We may need a stronger definition of heap equivalence.
 */
object LeftistHeapSpec0 {
  def insert_commu_lemma (h: Heap, p1: BigInt, p2: BigInt): Boolean = {
    require(isLeftistHeap(h))
    heapContent(insert(p2, insert(p1, h))) == heapContent(insert(p1, insert(p2, h)))
  } holds /* verified by Leon */

  def merge_commu_lemma (h1: Heap, h2: Heap): Boolean = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2))
    heapContent(merge(h1, h2)) == heapContent(merge(h2, h1))
  } holds /* verified by Leon */

  def merge_assoc_lemma (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2) && isLeftistHeap(h3))
    heapContent(merge(h1, merge(h2, h3))) == heapContent(merge(merge(h1, h2), h3))
  } holds /* verified by Leon */
}

/**
 * A leftist tree.
 * Each node maintains a "rank", which records the length of the path between
 * the node and the right most leaf.
 * Invariants:
 * 1. For each node, the height of its right subtree <= that of its left subtree.
 * 2. For each node, the rank of its right child <= the rank of its left child.
 */
object LeftistHeapOps {

  sealed abstract class Heap

  case object Leaf extends Heap

  case class Node (rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

  ////////// Interface functions ////////////

  def findMax (h: Heap): Option[BigInt] = {
    require(isLeftistHeap(h))
    h match {
      case Leaf             => None[BigInt]()
      case Node(_, v, _, _) => Some(v)
    }
  } ensuring { res => h != Leaf implies
    res.isDefined && {
      val Node(_, _, left, right) = h
      val m = res.get
      m >= max(findMax(left).getOrElse(m), findMax(right).getOrElse(m))
    }
  } /* verified by Leon */

  def removeMax (h: Heap): Heap = {
    require(isLeftistHeap(h))
    h match {
      case Node(_, _, l, r) => merge(l, r)
      case l@Leaf           => l
    }
  } ensuring { res =>
    size(res) >= size(h) - 1 &&
      heapContent(res).subsetOf(heapContent(h)) && {
      h != Leaf implies
        heapContent(h) == heapContent(res) ++ Set(findMax(h).get)
    }
  } /* verified by Leon */

  def merge (h1: Heap, h2: Heap): Heap = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2))
    h1 match {
      case Leaf                => h2
      case Node(_, v1, l1, r1) => h2 match {
        case Leaf                => h1
        case Node(_, v2, l2, r2) =>
          if (v1 > v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring { res =>
    isLeftistHeap(res) &&
      size(res) == size(h1) + size(h2) &&
      heapContent(res) == heapContent(h1) ++ heapContent(h2) && {
      res != Leaf implies {
        val v = findMax(res).get
        v == max(findMax(h1).getOrElse(v), findMax(h2).getOrElse(v))
      }
    }
  } /* verified by Leon */

  def insert (element: BigInt, heap: Heap): Heap = {
    require(isLeftistHeap(heap))
    merge(Node(1, element, Leaf, Leaf), heap)
  } ensuring { res => isLeftistHeap(res) &&
    size(res) == size(heap) + 1 &&
    heapContent(res) == heapContent(heap) ++ Set(element)
  } /* verified by Leon */

  def isLeftistHeap (h: Heap): Boolean = {
    h match {
      case Leaf                    => true
      case Node(_, v, left, right) =>
        isLeftistHeap(left) && isLeftistHeap(right) &&
          rightHeight(left) >= rightHeight(right) &&
          isPartiallyOrdered(v, left, right)
    }
  }

  def isPartiallyOrdered (value: BigInt, h1: Heap, h2: Heap) = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2))
    h1 match {
      case Leaf              => h2 match {
        case Leaf              => true
        case Node(_, v2, _, _) => value >= v2
      }
      case Node(_, v1, _, _) => value >= v1 && {
        h2 match {
          case Leaf              => true
          case Node(_, v2, _, _) => value >= v2
        }
      }
    }
  }

  def size (t: Heap): BigInt = {
    t match {
      case Leaf             => BigInt(0)
      case Node(_, v, l, r) => size(l) + 1 + size(r)
    }
  }

  ////////// Abstraction functions ////////////

  def heapContent (h: Heap): Set[BigInt] = h match {
    case Leaf                    => Set.empty[BigInt]
    case Node(_, v, left, right) => Set(v) ++ heapContent(left) ++ heapContent(right)
  }

  ///////////// Helper functions //////////////

  private def max (a: BigInt, b: BigInt) = {
    if (a > b) a else b
  } ensuring { res => res == a || res == b }

  private def rightHeight (h: Heap): BigInt = {
    h match {
      case Leaf             => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (_ >= 0)

  private def makeT (value: BigInt, left: Heap, right: Heap): Heap = {
    require(isLeftistHeap(left) && isLeftistHeap(right) &&
      isPartiallyOrdered(value, left, right))
    if (rightHeight(left) >= rightHeight(right))
      Node(rightHeight(right) + 1, value, left, right)
    else // swap left and right subtree
      Node(rightHeight(left) + 1, value, right, left)
  } ensuring {
    isLeftistHeap(_)
  } /* verified by Leon */
}