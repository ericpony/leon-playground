package duck.spec

import duck.proof.sugar._
import duck.collection._
import duck.spec.SortedListOps._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

object LeftistHeapSpec1 {

  case class Bisimulation (h1: Heap) {
    def ~ (h2: Heap): Boolean = permutation(h1.toList, h2.toList)
  }

  implicit def bisimulate (h: Heap) = Bisimulation(h)

  def insert_invariant (h1: Heap, h2: Heap, e: BigInt): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.insert(e) ~ h2.insert(e) because {
      val l1 = h1.insert(e).toList
      val l2 = h2.insert(e).toList
      permutation(l1, e :: h1.toList) &&
        permutation(e :: h2.toList, l2) &&
        //permutation(e :: h1.toList, e :: h2.toList) because
        permutation_cons(h1.toList, h2.toList, e) &&
        permutation_tran_lemma(l1, e :: h1.toList, e :: h2.toList) &&
        permutation_tran_lemma(l1, e :: h2.toList, l2)
    }
  } holds /* verified by Leon */

  def findMin_invariant (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.findMin == h2.findMin
  } holds /* verified by Leon */

  def merge_invariant (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap && h1 ~ h2)
    h1.merge(h2) ~ h1.merge(h2)
  } holds /* timeout */
}

@ignore
object LeftistHeapSpec0 {
  def insert_commu_prop (h: Heap, e1: BigInt, e2: BigInt): Boolean = {
    require(h.isLeftistHeap)
    h.insert(e1).insert(e2).content == h.insert(e2).insert(e1).content
  } holds /* verified by Leon */

  def merge_commu_prop (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    h1.merge(h2).content == h2.merge(h1).content
  } holds /* verified by Leon */

  def merge_assoc_prop (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap)
    h1.merge(h2).merge(h3).content == h1.merge(h2.merge(h3)).content
  } holds /* verified by Leon */

  def composition_prop (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L.content == L1.merge(L2).content
  } holds /* verified by Leon */

  def foldl_insert (heap: Heap, list: List[BigInt]): Heap = {
    require(heap.isLeftistHeap)
    if (list == Nil[BigInt]()) heap
    else foldl_insert(heap.insert(list.head), list.tail)
  } ensuring { res =>
    res.isLeftistHeap &&
      res.content == heap.content ++ list.content
  } /* verified by Leon */
}

/**
 * A leftist tree.
 * Each node maintains a "rank", which records the length of the path between
 * the node and the right most leaf.
 * Invariants:
 * 1. For each node, the height of its right subtree <= that of its left subtree.
 * 2. For each node, the rank of its right child <= the rank of its left child.
 */
@library
sealed abstract class Heap {

  def findMin: Option[BigInt] = {
    require(this.isLeftistHeap)
    this match {
      case Empty()          => None[BigInt]()
      case Node(_, v, _, _) => Some(v)
    }
  } ensuring { res => this != Empty() implies
    res.isDefined && {
      val Node(_, _, left, right) = this
      val m = res.get
      m <= min(left.findMin.getOrElse(m), right.findMin.getOrElse(m)) && {
        this != Empty() implies
          this.content == this.deleteMin.content ++ Set(m)
      }
    }
  } /* verified by Leon */

  def deleteMin: Heap = {
    require(this.isLeftistHeap)
    this match {
      case Node(_, _, l, r) => l.merge(r)
      case l@Empty()        => l
    }
  } ensuring { res =>
    res.size >= this.size - 1 &&
      res.content.subsetOf(this.content) && {
      this != Empty() && res != Empty() implies
        this.findMin.get <= res.findMin.get &&
          this.content == res.content ++ Set(this.findMin.get)
    }
  } /* verified by Leon */

  def merge (h: Heap): Heap = {
    require(this.isLeftistHeap && h.isLeftistHeap)
    this match {
      case Empty()             => h
      case Node(_, v1, l1, r1) => h match {
        case Empty()             => this
        case Node(_, v2, l2, r2) =>
          if (v1 <= v2)
            makeT(v1, l1, r1.merge(h))
          else
            makeT(v2, l2, this.merge(r2))
      }
    }
  } ensuring { res =>
    res.isLeftistHeap &&
      res.size == this.size + h.size &&
      res.content == this.content ++ h.content &&
      permutation(res.toList, this.toList ++ h.toList) && {
      res != Empty() implies {
        val v = res.findMin.get
        v == min(this.findMin.getOrElse(v), h.findMin.getOrElse(v))
      }
    }
  } /* timeout */

  def insert (element: BigInt): Heap = {
    require(this.isLeftistHeap)
    Node(1, element, Empty(), Empty()).merge(this)
  } ensuring { res => res.isLeftistHeap &&
    res.size == this.size + 1 &&
    res.content == this.content ++ Set(element) &&
    permutation(res.toList, element :: this.toList)
  } /* verified by Leon */

  def isLeftistHeap: Boolean = {
    this match {
      case Empty()                 => true
      case Node(_, v, left, right) =>
        left.isLeftistHeap && right.isLeftistHeap &&
          rightHeight(left) >= rightHeight(right) &&
          isPartiallyOrdered(v, left, right)
    }
  }

  def toList: List[BigInt] = {
    this match {
      case Empty()          => Nil[BigInt]()
      case Node(_, v, l, r) => v :: (l.toList ++ r.toList)
    }
  } ensuring { res =>
    res.size == this.size && res.content == this.content
  }

  @induct
  def toSortedList: List[BigInt] = {
    require(this.isLeftistHeap)
    this match {
      case Empty() => Nil[BigInt]()
      case _       => this.findMin.get :: this.deleteMin.toSortedList
    }
  } ensuring { res =>
    isSorted(res) && res.size == this.size
  }

  def isPartiallyOrdered (value: BigInt, h1: Heap, h2: Heap) = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    h1 match {
      case Empty()           => h2 match {
        case Empty()           => true
        case Node(_, v2, _, _) => value <= v2
      }
      case Node(_, v1, _, _) => value <= v1 && {
        h2 match {
          case Empty()           => true
          case Node(_, v2, _, _) => value <= v2
        }
      }
    }
  }

  def size: BigInt = {
    this match {
      case Empty()          => BigInt(0)
      case Node(_, v, l, r) => l.size + 1 + r.size
    }
  }

  ////////// Abstraction functions ////////////

  def content: Set[BigInt] =
    this match {
      case Empty()                 => Set.empty[BigInt]
      case Node(_, v, left, right) => Set(v) ++ left.content ++ right.content
    }

  ///////////// Helper functions //////////////

  private def min (a: BigInt, b: BigInt) = {
    if (a <= b) a else b
  } ensuring { res => res == a || res == b }

  private def rightHeight (h: Heap): BigInt = {
    h match {
      case Empty()          => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (_ >= 0)

  private def makeT (value: BigInt, left: Heap, right: Heap): Heap = {
    require(left.isLeftistHeap && right.isLeftistHeap &&
      isPartiallyOrdered(value, left, right))
    if (rightHeight(left) >= rightHeight(right))
      Node(rightHeight(right) + 1, value, left, right)
    else // swap left and right subtree
      Node(rightHeight(left) + 1, value, right, left)
  } ensuring { res =>
    res.isLeftistHeap &&
      permutation(res.toList, value :: (left.toList ++ right.toList))
  } /* verified by Leon */

  //  def ~ (h2: Heap): Boolean = permutation(this.toList, h2.toList)
}

case class Empty () extends Heap

case class Node (rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

/*
object LeftistHeapOps {
  ////////// Interface functions ////////////

  def findMin (h: Heap): Option[BigInt] = {
    require(isLeftistHeap(h))
    h match {
      case Empty()            => None[BigInt]()
      case Node(_, v, _, _) => Some(v)
    }
  } ensuring { res => h != Empty() implies
    res.isDefined && {
      val Node(_, _, left, right) = h
      val m = res.get
      m <= min(findMin(left).getOrElse(m), findMin(right).getOrElse(m)) && {
        h != Empty() implies
          heapContent(h) == heapContent(deleteMin(h)) ++ Set(m)
      }
    }
  } /* verified by Leon */

  def deleteMin (h: Heap): Heap = {
    require(isLeftistHeap(h))
    h match {
      case Node(_, _, l, r) => merge(l, r)
      case l@Empty()          => l
    }
  } ensuring { res =>
    size(res) >= size(h) - 1 &&
      heapContent(res).subsetOf(heapContent(h)) && {
      h != Empty() && res != Empty() implies
        findMin(h).get <= findMin(res).get &&
          heapContent(h) == heapContent(res) ++ Set(findMin(h).get)
    }
  } /* verified by Leon */

  def merge (h1: Heap, h2: Heap): Heap = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2))
    h1 match {
      case Empty()               => h2
      case Node(_, v1, l1, r1) => h2 match {
        case Empty()               => h1
        case Node(_, v2, l2, r2) =>
          if (v1 <= v2)
            makeT(v1, l1, merge(r1, h2))
          else
            makeT(v2, l2, merge(h1, r2))
      }
    }
  } ensuring { res =>
    isLeftistHeap(res) &&
      size(res) == size(h1) + size(h2) &&
      heapContent(res) == heapContent(h1) ++ heapContent(h2) && {
      res != Empty() implies {
        val v = findMin(res).get
        v == min(findMin(h1).getOrElse(v), findMin(h2).getOrElse(v))
      }
    }
  } /* verified by Leon */

  def insert (element: BigInt, heap: Heap): Heap = {
    require(isLeftistHeap(heap))
    merge(Node(1, element, Empty(), Empty()), heap)
  } ensuring { res => isLeftistHeap(res) &&
    size(res) == size(heap) + 1 &&
    heapContent(res) == heapContent(heap) ++ Set(element)
  } /* verified by Leon */

  def isLeftistHeap (h: Heap): Boolean = {
    h match {
      case Empty()                   => true
      case Node(_, v, left, right) =>
        isLeftistHeap(left) && isLeftistHeap(right) &&
          rightHeight(left) >= rightHeight(right) &&
          isPartiallyOrdered(v, left, right)
    }
  }

  def toList (h: Heap): List[BigInt] = {
    h match {
      case Empty()            => Nil[BigInt]()
      case Node(_, v, l, r) => v :: (toList(l) ++ toList(r))
    }
  } ensuring { res =>
    res.size == size(h) && res.content == heapContent(h)
  }

  @induct
  def toSortedList (h: Heap): List[BigInt] = {
    require(isLeftistHeap(h))
    h match {
      case Empty() => Nil[BigInt]()
      case _     => findMin(h).get :: toSortedList(deleteMin(h))
    }
  } ensuring { res =>
    isSorted(res) && res.size == size(h)
  }

  def isPartiallyOrdered (value: BigInt, h1: Heap, h2: Heap) = {
    require(isLeftistHeap(h1) && isLeftistHeap(h2))
    h1 match {
      case Empty()             => h2 match {
        case Empty()             => true
        case Node(_, v2, _, _) => value <= v2
      }
      case Node(_, v1, _, _) => value <= v1 && {
        h2 match {
          case Empty()             => true
          case Node(_, v2, _, _) => value <= v2
        }
      }
    }
  }

  def size (t: Heap): BigInt = {
    t match {
      case Empty()            => BigInt(0)
      case Node(_, v, l, r) => size(l) + 1 + size(r)
    }
  }

  ////////// Abstraction functions ////////////

  def heapContent (h: Heap): Set[BigInt] = h match {
    case Empty()                   => Set.empty[BigInt]
    case Node(_, v, left, right) => Set(v) ++ heapContent(left) ++ heapContent(right)
  }

  ///////////// Helper functions //////////////

  private def min (a: BigInt, b: BigInt) = {
    if (a <= b) a else b
  } ensuring { res => res == a || res == b }

  private def rightHeight (h: Heap): BigInt = {
    h match {
      case Empty()            => BigInt(0)
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
*/