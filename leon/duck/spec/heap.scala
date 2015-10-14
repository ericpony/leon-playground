package duck.spec

import duck.proof.sugar._
import duck.collection._
import duck.spec.SortedListOps._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.PermutationSpec._
import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions
import LeftistHeapOps._
import LeftistHeapLemmas._

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
    h1.merge(h3) ~ h2.merge(h3) because {
      val l1 = h1.merge(h3).toList
      val l2 = h2.merge(h3).toList
      // permutation(l1, h1.toList ++ h3.toList) because
      merge_concat_lemma(h1, h3) &&
        // permutation(l2, h2.toList ++ h3.toList) because
        merge_concat_lemma(h2, h3) &&
        // permutation(h1.toList ++ h3.toList, h2.toList ++ h3.toList) because
        permutation_append(h1.toList, h2.toList, h3.toList) &&
        permutation_tran(l1, h1.toList ++ h3.toList, h2.toList ++ h3.toList) &&
        permutation_tran(l1, h2.toList ++ h3.toList, l2)
    }
  } holds /* verified by Leon */
}

@library
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
      res.content == this.content ++ h.content && {
      //      permutation(res.toList, this.toList ++ h.toList) && {
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

  //  def ~ (h2: Heap): Boolean = permutation(this.toList, h2.toList)
}

object LeftistHeapOps {
  def rightHeight (h: Heap): BigInt = {
    h match {
      case Empty()          => BigInt(0)
      case Node(_, _, _, r) => rightHeight(r) + 1
    }
  } ensuring (_ >= 0)

  def makeT (v: BigInt, l: Heap, r: Heap): Heap = {
    require(l.isLeftistHeap && r.isLeftistHeap &&
      isPartiallyOrdered(v, l, r))
    if (rightHeight(l) >= rightHeight(r))
      Node(rightHeight(r) + 1, v, l, r)
    else // swap l and r subtree
      Node(rightHeight(l) + 1, v, r, l)
  } ensuring { res =>
    res.isLeftistHeap &&
      permutation(res.toList, v :: (l.toList ++ r.toList))
  } /* verified by Leon */

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

}

case class Empty () extends Heap

case class Node (rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

object LeftistHeapLemmas {
  /**
   * Warning: Need at most 20+ seconds to be verified on my desktop
   */
  def merge_concat_lemma (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    permutation(h1.merge(h2).toList, h1.toList ++ h2.toList) because {
      h1 match {
        case Empty()             => check { permutation_refl(h2.toList) }
        case Node(_, v1, l1, r1) => h2 match {
          case Empty()             => check { permutation_refl(h1.toList) } //trivial
          case Node(_, v2, l2, r2) =>
            val h = h1.merge(h2)
            if (v1 <= v2) {
              val l = l1
              val r = r1.merge(h2)
              /* h == makeT(v1, l, r) */
              // permutation((l1.toList ++ r1.toList) ++ h2.toList, l1.toList ++ r1.toList ++ h2.toList) because
              permutation_concat_assoc2(l1.toList, r1.toList, h2.toList) &&
                // permutation(v1 :: ((l1.toList ++ r1.toList) ++ h2.toList), v1 :: (l1.toList ++ r1.toList ++ h2.toList)) because
                permutation_cons((l1.toList ++ r1.toList) ++ h2.toList, l1.toList ++ r1.toList ++ h2.toList, v1) &&
                h1.toList ++ h2.toList == v1 :: ((l1.toList ++ r1.toList) ++ h2.toList) &&
                permutation(l.toList ++ r.toList, l1.toList ++ r1.toList ++ h2.toList) because {
                // permutation(r.toList, r1.toList ++ h2.toList) because
                merge_concat_lemma(r1, h2) &&
                  permutation_concat(l.toList, r.toList, r1.toList ++ h2.toList) &&
                  // permutation(l1.toList ++ r1.toList ++ h2.toList, l1.toList ++ (r1.toList ++ h2.toList)) because
                  permutation_concat_assoc(l1.toList, r1.toList, h2.toList) &&
                  permutation_tran(l.toList ++ r.toList, l1.toList ++ (r1.toList ++ h2.toList), l1.toList ++ r1.toList ++ h2.toList)
              } &&
                // permutation(v1 :: (l.toList ++ r.toList), v1 :: (l1.toList ++ r1.toList ++ h2.toList)) because
                permutation_cons(l.toList ++ r.toList, l1.toList ++ r1.toList ++ h2.toList, v1) &&
                permutation(h1.toList ++ h2.toList, v1 :: (l.toList ++ r.toList)) &&
                permutation(h.toList, v1 :: (l.toList ++ r.toList)) &&
                permutation_tran(h.toList, v1 :: (l.toList ++ r.toList), h1.toList ++ h2.toList)
            } else {
              val l = l2
              val r = h1.merge(r2)
              /* h == makeT(v2, l, r) */
              // permutation(h.toList, v2 :: (l.toList ++ r.toList)) &&
              // permutation(h.toList, v2 :: (l.toList ++ r.toList)) because
              merge_concat_lemma(h1, r2) &&
                permutation(r.toList, h1.toList ++ r2.toList) &&
                // permutation(l.toList ++ (r2.toList ++ h1.toList), l.toList ++ (h1.toList ++ r2.toList)) because {
                permutation_concat_comm(h1.toList, r2.toList) &&
                permutation_concat(l.toList, r2.toList ++ h1.toList, h1.toList ++ r2.toList) && // }
                // permutation(l.toList ++ (r2.toList ++ h1.toList), (l.toList ++ r2.toList) ++ h1.toList) because
                permutation_concat_assoc(l.toList, r2.toList, h1.toList) &&
                // permutation(l.toList ++ (h1.toList ++ r2.toList), (l.toList ++ r2.toList) ++ h1.toList) because
                permutation_tran(
                  l.toList ++ (h1.toList ++ r2.toList),
                  l.toList ++ (r2.toList ++ h1.toList),
                  (l.toList ++ r2.toList) ++ h1.toList
                ) &&
                // permutation(r.toList, h1.toList ++ r2.toList) because
                merge_concat_lemma(h1, r2) &&
                permutation_concat(l.toList, r.toList, h1.toList ++ r2.toList) &&
                permutation_tran(
                  l.toList ++ r.toList,
                  l.toList ++ (h1.toList ++ r2.toList),
                  (l.toList ++ r2.toList) ++ h1.toList
                ) &&
                // permutation(v2 :: (l.toList ++ (h1.toList ++ r2.toList)), v2 :: (l.toList ++ r2.toList) ++ h1.toList) because
                permutation_cons(l.toList ++ r.toList, (l.toList ++ r2.toList) ++ h1.toList, v2) &&
                permutation_eq(h2.toList ++ h1.toList, v2 :: (l.toList ++ r2.toList) ++ h1.toList) &&
                permutation_tran(h.toList, v2 :: (l.toList ++ r.toList), v2 :: (l.toList ++ r2.toList) ++ h1.toList) &&
                permutation_tran(h.toList, v2 :: (l.toList ++ r2.toList) ++ h1.toList, h2.toList ++ h1.toList) &&
                permutation(h2.toList ++ h1.toList, h1.toList ++ h2.toList) &&
                permutation_concat_comm(h1.toList, h2.toList) &&
                permutation_tran(h.toList, h2.toList ++ h1.toList, h1.toList ++ h2.toList)
            }
        }
      }
    }
  } holds /* verified by Leon */
}