package duck.spec

import duck.proof.sugar._
import duck.collection._
import duck.spec.SortedListOps._
import duck.proof.PermutationOps._
import duck.proof.PermutationLemmas._
import duck.proof.PermutationSpec._
import duck.proof.MinOps._
import duck.proof.MinLemmas._
import duck.proof.DeleteOps._

import leon.lang._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import scala.language.implicitConversions

import LeftistHeapOps._
import LeftistHeapLemmas1._

/**
 * LeftistHeap as List
 */
object LeftistHeapSpec1 {

  /**
   * h1 ~ h2 implies h1.insert(e) ~ h2.insert(e)
   */
  def insert_invariant (h1: Heap, h2: Heap, e: BigInt): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.insert(e) ~ h2.insert(e) because {
      val l1 = h1.insert(e)
      val l2 = h2.insert(e)
      heap_insert_lemma(h1, e) &&
        heap_insert_lemma(h2, e) &&
        permutation_cons(h1, h2, e) &&
        permutation_tran_lemma(l1, e :: h1, e :: h2) &&
        permutation_tran_lemma(l1, e :: h2, l2)
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ h2 implies h1.merge(h) ~ h2.merge(h)
   */
  def merge_invariant (h1: Heap, h2: Heap, h: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h.isLeftistHeap && h1 ~ h2)
    h1.merge(h) ~ h2.merge(h) because {
      val l1 = h1.merge(h)
      val l2 = h2.merge(h)
      heap_merge_lemma(h1, h) &&
        heap_merge_lemma(h2, h) &&
        permutation_append(h1, h2, h) &&
        permutation_tran(l1, h1 ++ h, h2 ++ h) &&
        permutation_tran(l1, h2 ++ h, l2)
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ h2 implies h1.findMin == h2.findMin
   */
  def findMin_invariant (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.findMin == h2.findMin because {
      if (h1 == Empty() || h2 == Empty())
        trivial
      else {
        findMin_lemma(h1) &&
          findMin_lemma(h2) &&
          min_permutation(h1, h2)
      }
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ h2 implies h1.deleteMin ~ h2.deleteMin
   */
  def deleteMin_invariant (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.deleteMin ~ h2.deleteMin because {
      if (h1 == Empty() || h2 == Empty())
        trivial
      else {
        findMin_invariant(h1, h2) &&
          permutation_delete(h1, h2, h1.findMin.get)
      }
    }
  } holds /* verified by Leon */

  /**
   * h1 ~ h2 implies h1.size == h2.size
   */
  def size_invariant (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.size == h2.size
  } holds /* verified by Leon */

  /**
   * h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1)
   */
  def insert_commu_prop (h: Heap, e1: BigInt, e2: BigInt): Boolean = {
    require(h.isLeftistHeap)
    h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1) because {
      heap_insert_lemma(h, e1) &&
        heap_insert_lemma(h, e2) &&
        heap_insert_lemma(h.insert(e1), e2) &&
        heap_insert_lemma(h.insert(e2), e1) &&
        permutation_cons(h.insert(e1), e1 :: h, e2) &&
        permutation_cons(h.insert(e2), e2 :: h, e1) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: h.insert(e1), e2 :: e1 :: h) &&
        permutation_tran(h.insert(e2).insert(e1), e1 :: h.insert(e2), e1 :: e2 :: h) &&
        permutation_prefix_comm(e1, e2, h) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: e1 :: h, e1 :: e2 :: h) &&
        permutation_tran(h.insert(e1).insert(e2), e1 :: e2 :: h, h.insert(e2).insert(e1))
    }
  } holds /* verified by Leon */

  /**
   * h1.merge(h2) ~ h2.merge(h1)
   */
  def merge_commu_prop (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    h1.merge(h2) ~ h2.merge(h1) because {
      heap_merge_lemma(h1, h2) &&
        heap_merge_lemma(h2, h1) &&
        permutation_concat_comm(h1, h2) &&
        permutation_tran(h1.merge(h2), h1 ++ h2, h2 ++ h1) &&
        permutation_tran(h1.merge(h2), h2 ++ h1, h2.merge(h1))
    }
  } holds /* verified by Leon */

  /**
   * (h1.merge(h2)).merge(h3) ~ h1.merge(h2.merge(h3))
   */
  def merge_assoc_prop (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap)
    h1.merge(h2).merge(h3) ~ h1.merge(h2.merge(h3)) because {
      heap_merge_lemma(h1, h2) &&
        heap_merge_lemma(h1.merge(h2), h3) &&
        permutation_append(h1.merge(h2), h1 ++ h2, h3) &&
        permutation_tran(h1.merge(h2).merge(h3), h1.merge(h2) ++ h3, h1 ++ h2 ++ h3) &&
        heap_merge_lemma(h2, h3) &&
        heap_merge_lemma(h1, h2.merge(h3)) &&
        permutation_prepend(h1, h2.merge(h3), h2 ++ h3) &&
        permutation_tran(h1.merge(h2.merge(h3)), h1 ++ h2.merge(h3), h1 ++ (h2 ++ h3)) &&
        permutation_concat_assoc(h1, h2, h3) &&
        permutation_tran(h1.merge(h2).merge(h3), h1 ++ h2 ++ h3, h1 ++ (h2 ++ h3)) &&
        permutation_tran(h1.merge(h2).merge(h3), h1 ++ (h2 ++ h3), h1.merge(h2.merge(h3)))
    }
  } holds /* verified by Leon */

  /**
   * foldl(Empty(), insert, l1 ++ l2) ==
   * foldl(Empty(), insert, l1).merge(foldl(Empty(), insert, l2))
   */
  def composition_prop (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L ~ L1.merge(L2) because {
      foldl_insert_lemma(Empty(), l1 ++ l2) &&
        foldl_insert_lemma(Empty(), l1) &&
        foldl_insert_lemma(Empty(), l2) &&
        heap_merge_lemma(L1, L2) &&
        permutation_append(L1, l1, l2) &&
        permutation_prepend(L1, L2, l2) &&
        permutation_tran(L1 ++ L2, L1 ++ l2, l1 ++ l2) &&
        permutation_tran(L1 ++ L2, l1 ++ l2, L) &&
        permutation_tran(L, L1 ++ L2, L1.merge(L2))
    }
  } holds /* verified by Leon */
}

/**
 * LeftistHeap as Set
 */
object LeftistHeapSpec0 {

  def insert_commu_prop (h: Heap, e1: BigInt, e2: BigInt): Boolean = {
    require(h.isLeftistHeap)
    h.insert(e1).insert(e2) ~~ h.insert(e2).insert(e1)
  } holds /* verified by Leon */

  def merge_commu_prop (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    h1.merge(h2) ~~ h2.merge(h1)
  } holds /* verified by Leon */

  def merge_assoc_prop (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap)
    h1.merge(h2).merge(h3) ~~ h1.merge(h2.merge(h3))
  } holds /* verified by Leon */

  def composition_prop (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L ~~ L1.merge(L2)
  } holds /* verified by Leon */
}

/**
 * A leftist heap.
 * Each node maintains a "rank", which records the length of the path between
 * the node and the right most leaf.
 * Invariants:
 * 1. For each node, the height of its right subtree <= that of its left subtree.
 * 2. For each node, the rank of its right child <= the rank of its left child.
 */

sealed abstract class Heap {

  def findMin: Option[BigInt] = {
    require(this.isLeftistHeap)
    this match {
      case Empty()          => None[BigInt]()
      case Node(_, v, _, _) => Some(v)
    }
  } ensuring { res => this != Empty() implies
    res.isDefined && {
      val m = res.get
      val Node(_, _, left, right) = this
      val p1 = m <= min(left.findMin.getOrElse(m), right.findMin.getOrElse(m))
      val p2 = this.content == this.deleteMin.content ++ Set(m)
      p1 && p2
    }
  } /* verified by Leon */

  def deleteMin: Heap = {
    require(this.isLeftistHeap)
    this match {
      case Empty()          => this
      case Node(_, _, l, r) => l.merge(r)
    }
  } ensuring {
    res =>
      res.size >= this.size - 1 &&
        res.toList == this.toList.tail &&
        res.content.subsetOf(this.content) && {
        this != Empty() && res != Empty() implies
          this.findMin.get <= res.findMin.get &&
            this.content == res.content ++ Set(this.findMin.get) &&
            permutation(res, delete(this, this.findMin.get))
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
  } ensuring {
    res =>
      res.isLeftistHeap &&
        res.size == this.size + h.size &&
        res.content == this.content ++ h.content && {
        res != Empty() implies {
          val v = res.findMin.get
          v == min(this.findMin.getOrElse(v), h.findMin.getOrElse(v))
        }
      }
  } /* verified by Leon */

  def insert (element: BigInt): Heap = {
    require(this.isLeftistHeap)
    this.merge(Node(1, element, Empty(), Empty()))
    // Node(1, element, Empty(), Empty()).merge(this)
  } ensuring {
    res =>
      res.isLeftistHeap &&
        res.size == this.size + 1 &&
        res.content == this.content ++ Set(element)
  } /* verified by Leon */

  def isLeftistHeap: Boolean = this match {
    case Empty()                 => true
    case Node(_, v, left, right) =>
      left.isLeftistHeap && right.isLeftistHeap &&
        rightHeight(left) >= rightHeight(right) &&
        isPartiallyOrdered(v, left, right)
  }

  def size: BigInt = {
    this match {
      case Empty()          => BigInt(0)
      case Node(_, v, l, r) => l.size + 1 + r.size
    }
  }

  def content: Set[BigInt] = this match {
    case Empty()                 => Set.empty[BigInt]
    case Node(_, v, left, right) => Set(v) ++ left.content ++ right.content
  }

  def toList: List[BigInt] = {
    this match {
      case Empty()          => Nil[BigInt] ()
      case Node(_, v, l, r) => v :: (l.toList ++ r.toList)
    }
  } ensuring {
    res =>
      res.size == this.size &&
        res.content == this.content &&
        (this != Empty() implies {
          val Node(_, v, l, r) = this
          permutation(this, v :: (l ++ r))
        })
  }

  @induct
  def toSortedList: List[BigInt] = {
    require(this.isLeftistHeap)
    this match {
      case Empty() => Nil[BigInt] ()
      case _       => this.findMin.get :: this.deleteMin.toSortedList
    }
  } ensuring {
    res =>
      isSorted(res) && res.size == this.size
  }
}

object Heap {

  case class Bisimulation (h1: Heap) {
    def ~ (h2: Heap): Boolean = permutation(h1, h2)

    def ~~ (h2: Heap): Boolean = h1.content == h2.content
  }

  implicit def bisimulate (h: Heap): Bisimulation = Bisimulation(h)

  implicit def toList (h: Heap): List[BigInt] = h.toList
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
      permutation(res, v :: (l ++ r)) because {
      if (rightHeight(l) >= rightHeight(r)) true
      else {
        permutation(res, v :: (r ++ l)) &&
          permutation_concat_comm(l, r) &&
          permutation_cons(r ++ l, l ++ r, v) &&
          permutation_tran(res, v :: (r ++ l), v :: (l ++ r))
      }
    }
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

  def foldl_insert (heap: Heap, list: List[BigInt]): Heap = {
    require(heap.isLeftistHeap)
    if (list == Nil[BigInt] ()) heap
    else foldl_insert(heap.insert(list.head), list.tail)
  } ensuring {
    res => res.isLeftistHeap &&
      res.content == (heap.content ++ list.content)
  } /* verified by Leon */
}

case class Empty () extends Heap

case class Node (rk: BigInt, value: BigInt, left: Heap, right: Heap) extends Heap

object LeftistHeapLemmas1 {

  def List (e: BigInt) = Cons(e, Nil[BigInt]())

  @induct
  def list_decomposition (l1: List[BigInt], l2: List[BigInt], e: BigInt) = {
    l1 ++ (e :: l2) == (l1 ++ List(e)) ++ l2
  } holds

  @induct
  def permutation_first_last_swap (l: List[BigInt], e: BigInt) = {
    permutation(e :: l, l ++ List(e))
  } holds

  @induct
  def permutation_prefix_comm (a: BigInt, b: BigInt, l: List[BigInt]) = {
    permutation(a :: b :: l, b :: a :: l)
  } holds

  /**
   * WARNING: Need ~20 sec. to be verified on my desktop
   */
  def heap_insert_lemma (h: Heap, e: BigInt): Boolean = {
    require(h.isLeftistHeap)
    permutation(h.insert(e), e :: h) because {
      if (h == Empty()) trivial
      else {
        val Node(_, v, l, r) = h
        val H = h.insert(e)
        if (v <= e) {
          h.insert(e) == makeT(v, l, r.merge(Node(1, e, Empty(), Empty()))) &&
            // permutation(H, v :: (l ++ r.insert(e))) &&
            // permutation(h, v :: (l ++ r)) &&
            // permutation((l ++ List(e)) ++ r, (List(e) ++ l) ++ r) because {
            permutation_concat_comm(l, List(e)) &&
            permutation_append(l ++ List(e), List(e) ++ l, r) && // }
            // permutation(e :: (l ++ r), (List(e) ++ l) ++ r) because
            permutation_eq(e :: (l ++ r), (List(e) ++ l) ++ r) &&
            // permutation(l ++ (e :: r), (l ++ List(e)) ++ r) because
            list_decomposition(l, r, e) &&
            permutation_eq(l ++ (e :: r), (l ++ List(e)) ++ r) &&
            permutation_tran((l ++ List(e)) ++ r, (List(e) ++ l) ++ r, e :: (l ++ r)) &&
            permutation_tran(l ++ (e :: r), (l ++ List(e)) ++ r, e :: (l ++ r)) &&
            // permutation(r.insert(e), e :: r) because
            heap_insert_lemma(r, e) &&
            // permutation(l ++ (e::r), l ++ r.insert(e)) because
            permutation_prepend(l, r.insert(e), e :: r) &&
            permutation_tran(l ++ r.insert(e), l ++ (e :: r), e :: (l ++ r)) &&
            permutation_tran(l ++ r.insert(e), l ++ (e :: r), e :: (l ++ r)) &&
            // permutation(v :: (l ++ r.insert(e)), v :: (e :: (l ++ r))) because
            permutation_cons(l ++ r.insert(e), e :: (l ++ r), v) &&
            // permutation(H, v :: e :: (l ++ r)) because
            permutation_tran(H, v :: (l ++ r.insert(e)), v :: e :: (l ++ r)) &&
            permutation_prefix_comm(v, e, l ++ r) &&
            permutation_tran(H, v :: e :: (l ++ r), e :: v :: (l ++ r)) &&
            permutation_cons(h, v :: (l ++ r), e) &&
            permutation_tran(H, e :: v :: (l ++ r), e :: h) &&
            permutation(H, e :: h)
        } else {
          h.insert(e) == makeT(e, Empty(), h.merge(Empty())) &&
            permutation(H, e :: h)
        }
      }
    }
  } holds

  /**
   * Warning: Need ~20 sec. to be verified on my desktop
   */
  def heap_merge_lemma (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    permutation(h1.merge(h2), h1 ++ h2) because {
      h1 match {
        case Empty()             => permutation_refl(h2)
        case Node(_, v1, l1, r1) => h2 match {
          case Empty()             => permutation_refl(h1)
          case Node(_, v2, l2, r2) =>
            val h = h1.merge(h2)
            if (v1 <= v2) {
              val l = l1
              val r = r1.merge(h2)
              //// h == makeT(v1, l, r) ////
              // permutation((L1 ++ R1) ++ H2, L1 ++ R1 ++ H2) because
              permutation_concat_assoc2(l1, r1, h2) &&
                // permutation(v1 :: ((l1 ++ r1) ++ h2), v1 :: (l1 ++ r1 ++ h2)) because
                permutation_cons((l1 ++ r1) ++ h2, l1 ++ r1 ++ h2, v1) &&
                h1 ++ h2 == v1 :: ((l1 ++ r1) ++ h2) &&
                // permutation(L ++ R, l1 ++ r1 ++ h2) because {
                // permutation(R, r1 ++ h2) because
                heap_merge_lemma(r1, h2) &&
                permutation_prepend(l, r, r1 ++ h2) &&
                // permutation(l1 ++ r1 ++ h2, l1 ++ (r1 ++ h2)) because
                permutation_concat_assoc(l1, r1, h2) &&
                permutation_tran(l ++ r, l1 ++ (r1 ++ h2), l1 ++ r1 ++ h2) && // }
                // permutation(h1 ++ h2, v1 :: (l ++ r)) because
                // permutation(v1 :: (l ++ r), v1 :: (l1 ++ r1 ++ h2)) because
                permutation_cons(l ++ r, l1 ++ r1 ++ h2, v1) &&
                // permutation(h, v1 :: (l ++ r)) by post-cond of toList
                permutation_tran(h, v1 :: (l ++ r), h1 ++ h2)
            } else {
              val l = l2
              val r = h1.merge(r2)
              //// h == makeT(v2, l, r) ////
              // permutation(h, v2 :: (l ++ r))
              // permutation(r, h1 ++ r2) because
              heap_merge_lemma(h1, r2) &&
                // permutation(l ++ (r2 ++ h1), l ++ (h1 ++ r2)) because {
                permutation_concat_comm(h1, r2) &&
                permutation_prepend(l, r2 ++ h1, h1 ++ r2) && // }
                // permutation(l ++ (r2 ++ h1), (l ++ r2) ++ h1) because
                permutation_concat_assoc(l, r2, h1) &&
                // permutation(l ++ (h1 ++ r2), (l ++ r2) ++ h1) because
                permutation_tran(l ++ (h1 ++ r2), l ++ (r2 ++ h1), (l ++ r2) ++ h1) &&
                // permutation(r, h1 ++ r2) because
                heap_merge_lemma(h1, r2) &&
                permutation_prepend(l, r, h1 ++ r2) &&
                permutation_tran(l ++ r, l ++ (h1 ++ r2), (l ++ r2) ++ h1) &&
                // permutation(v2 :: (l ++ (h1 ++ r2)), v2 :: (l ++ r2) ++ h1) because
                permutation_cons(l ++ r, (l ++ r2) ++ h1, v2) &&
                permutation_eq(h2 ++ h1, v2 :: (l ++ r2) ++ h1) &&
                permutation_tran(h, v2 :: (l ++ r), v2 :: (l ++ r2) ++ h1) &&
                permutation_tran(h, v2 :: (l ++ r2) ++ h1, h2 ++ h1) &&
                // permutation(h2 ++ h1, h1 ++ h2) because
                permutation_concat_comm(h1, h2) &&
                permutation_tran(h, h2 ++ h1, h1 ++ h2)
            }
        }
      }
    }
  } holds /* verified by Leon */

  def foldl_insert_lemma (heap: Heap, list: List[BigInt]): Boolean = {
    require(heap.isLeftistHeap)
    permutation(foldl_insert(heap, list), heap ++ list) because {
      if (list == Nil[BigInt]()) trivial
      else {
        val H = foldl_insert(heap, list)
        val Cons(h, t) = list
        H == foldl_insert(heap.insert(h), t) &&
          // permutation(H.toList, heap.insert(h) ++ t) because
          foldl_insert_lemma(heap.insert(h), t) &&
          heap_insert_lemma(heap, h) &&
          permutation_append(heap.insert(h), h :: heap, t) &&
          permutation_tran(H, heap.insert(h) ++ t, (h :: heap) ++ t) &&
          permutation_first_last_swap(heap, h) &&
          permutation_append(h :: heap, heap ++ List(h), t) &&
          list_decomposition(heap, t, h) &&
          permutation_tran(H, (h :: heap) ++ t, heap ++ list)
      }
    }
  } holds /* verified by Leon */

  def findMin_lemma (h: Heap): Boolean = {
    require(h.isLeftistHeap)
    (h == Empty() || h.findMin.get == min(h.toList)) because {
      if (h == Empty())
        trivial
      else {
        val Node(_, v, l, r) = h
        if (l == Empty() && r == Empty())
          trivial
        else {
          // h.findMin.get <= min(l) because
          findMin_lemma(l) &&
            // h.findMin.get <= min(r) because
            findMin_lemma(r) &&
            // min(min(l), min(r)) == min(l ++ r) because
            min_concat_lemma(l, r)
        }
      }
    }
  } holds /* verified by Leon */

  def min_permutation (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(permutation(l1, l2) && l2 != Nil[BigInt]())
    min(l1) == min(l2) because {
      if (l1.size == 1)
        trivial
      else {
        val l11 = delete(l1, min(l1))
        val l21 = delete(l2, min(l1))
        //min(l11) == min(l21) because {
        permutation_delete(l1, l2, min(l1)) &&
          min_permutation(l11, l21) && // }
          // min(l1) <= min(l21) because
          // min(l1) <= min(l11) because
          min_contains(l1, min(l11)) &&
          // l2.contains(min(l1)) &&
          min_delete(l2, min(l1))
      }
    }
  } holds /* verified by Leon */

  @induct
  def min_delete (l: List[BigInt], m: BigInt): Boolean = {
    require(l.contains(m) &&
      (l.size == 1 || m <= min(delete(l, m))))
    m == min(l)
  } holds /* verified by Leon */
}