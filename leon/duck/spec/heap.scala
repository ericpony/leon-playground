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
import LeftistHeapLemmas1._

/**
 * TODO: prove merge_commu_prop, merge_assoc_prop, composition_prop
 */
object LeftistHeapSpec1 {

  @library
  def insert_invariant (h1: Heap, h2: Heap, e: BigInt): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.insert(e) ~ h2.insert(e) because {
      val l1 = h1.insert(e)
      val l2 = h2.insert(e)
      permutation(l1, e :: h1) &&
        permutation(e :: h2, l2) &&
        //permutation(e :: h1, e :: h2) because
        permutation_cons(h1, h2, e) &&
        permutation_tran_lemma(l1, e :: h1, e :: h2) &&
        permutation_tran_lemma(l1, e :: h2, l2)
    }
  } holds /* verified by Leon */

  @library
  def findMin_invariant (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h1 ~ h2)
    h1.findMin == h2.findMin
  } holds /* verified by Leon */

  @library
  def merge_invariant (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap && h1 ~ h2)
    h1.merge(h3) ~ h2.merge(h3) because {
      val l1 = h1.merge(h3)
      val l2 = h2.merge(h3)
      // permutation(l1, h1 ++ h3) because
      merge_concat_lemma(h1, h3) &&
        // permutation(l2, h2 ++ h3) because
        merge_concat_lemma(h2, h3) &&
        // permutation(h1 ++ h3, h2 ++ h3) because
        permutation_append(h1, h2, h3) &&
        permutation_tran(l1, h1 ++ h3, h2 ++ h3) &&
        permutation_tran(l1, h2 ++ h3, l2)
    }
  } holds /* verified by Leon */

  def insert_commu_prop (h: Heap, e1: BigInt, e2: BigInt): Boolean = {
    require(h.isLeftistHeap)
    h.insert(e1).insert(e2) ~ h.insert(e2).insert(e1) because {
      //permutation(h.insert(e1), e1 :: h) because
      insert_cons_lemma(h, e1) &&
        insert_cons_lemma(h, e2) &&
        insert_cons_lemma(h.insert(e1), e2) &&
        insert_cons_lemma(h.insert(e2), e1) &&
        permutation_cons(h.insert(e1), e1 :: h, e2) &&
        permutation_cons(h.insert(e2), e2 :: h, e1) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: h.insert(e1), e2 :: e1 :: h) &&
        permutation_tran(h.insert(e2).insert(e1), e1 :: h.insert(e2), e1 :: e2 :: h) &&
        permutation_prefix_comm(e1, e2, h) &&
        permutation_tran(h.insert(e1).insert(e2), e2 :: e1 :: h, e1 :: e2 :: h) &&
        permutation_tran(h.insert(e1).insert(e2), e1 :: e2 :: h, h.insert(e2).insert(e1))
    }
  } holds /* verified by Leon */

  def merge_commu_prop (h1: Heap, h2: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap)
    h1.merge(h2) ~ h2.merge(h1)
  } holds /* timeout */

  def merge_assoc_prop (h1: Heap, h2: Heap, h3: Heap): Boolean = {
    require(h1.isLeftistHeap && h2.isLeftistHeap && h3.isLeftistHeap)
    h1.merge(h2).merge(h3) ~ h1.merge(h2.merge(h3))
  } holds /* timeout */

  def composition_prop (l1: List[BigInt], l2: List[BigInt]): Boolean = {
    val L = foldl_insert(Empty(), l1 ++ l2)
    val L1 = foldl_insert(Empty(), l1)
    val L2 = foldl_insert(Empty(), l2)
    L ~ L1.merge(L2)
  } holds /* timeout */

  def foldl_insert (heap: Heap, list: List[BigInt]): Heap = {
    require(heap.isLeftistHeap)
    if (list == Nil[BigInt]()) heap
    else foldl_insert(heap.insert(list.head), list.tail)
  } ensuring { res =>
    res.isLeftistHeap &&
      permutation(res, heap ++ list)
  }
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
  } ensuring { res =>
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

  def toList: List[BigInt] = {
    this match {
      case Empty()          => Nil[BigInt]()
      case Node(_, v, l, r) => v :: (l.toList ++ r.toList)
    }
  } ensuring { res =>
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
}

object Heap {

  case class Bisimulation (h1: Heap) {
    def ~ (h2: Heap): Boolean = permutation(h1, h2)
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
      permutation(res, v :: (l ++ r))
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

object LeftistHeapLemmas1 {

  def List (e: BigInt) = Cons(e, Nil[BigInt]())

  @induct
  def list_decomp (l1: List[BigInt], l2: List[BigInt], e: BigInt) = {
    l1 ++ (e :: l2) == (l1 ++ List(e)) ++ l2
  } holds

  @induct
  def permutation_prefix_comm (a: BigInt, b: BigInt, l: List[BigInt]) = {
    permutation(a :: b :: l, b :: a :: l)
  } holds

  /**
   * WARNING: Need ~20 sec. to be verified on my desktop
   */
  def insert_cons_lemma (h: Heap, e: BigInt): Boolean = {
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
            list_decomp(l, r, e) &&
            permutation_eq(l ++ (e :: r), (l ++ List(e)) ++ r) &&
            permutation_tran((l ++ List(e)) ++ r, (List(e) ++ l) ++ r, e :: (l ++ r)) &&
            permutation_tran(l ++ (e :: r), (l ++ List(e)) ++ r, e :: (l ++ r)) &&
            // permutation(r.insert(e), e :: r) because
            insert_cons_lemma(r, e) &&
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
  def merge_concat_lemma (h1: Heap, h2: Heap): Boolean = {
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
              /* h == makeT(v1, l, r) */
              // permutation((L1 ++ R1) ++ H2, L1 ++ R1 ++ H2) because
              permutation_concat_assoc2(l1, r1, h2) &&
                // permutation(v1 :: ((l1 ++ r1) ++ h2), v1 :: (l1 ++ r1 ++ h2)) because
                permutation_cons((l1 ++ r1) ++ h2, l1 ++ r1 ++ h2, v1) &&
                h1 ++ h2 == v1 :: ((l1 ++ r1) ++ h2) &&
                // permutation(L ++ R, l1 ++ r1 ++ h2) because {
                // permutation(R, r1 ++ h2) because
                merge_concat_lemma(r1, h2) &&
                permutation_prepend(l, r, r1 ++ h2) &&
                // permutation(l1 ++ r1 ++ h2, l1 ++ (r1 ++ h2)) because
                permutation_concat_assoc(l1, r1, h2) &&
                permutation_tran(l ++ r, l1 ++ (r1 ++ h2), l1 ++ r1 ++ h2) && // }
                // permutation(v1 :: (l ++ r), v1 :: (l1 ++ r1 ++ h2)) because
                permutation_cons(l ++ r, l1 ++ r1 ++ h2, v1) &&
                permutation(h1 ++ h2, v1 :: (l ++ r)) &&
                permutation(h, v1 :: (l ++ r)) &&
                permutation_tran(h, v1 :: (l ++ r), h1 ++ h2)
            } else {
              val l = l2
              val r = h1.merge(r2)
              /* h == makeT(v2, l, r) */
              // permutation(h, v2 :: (l ++ r)) &&
              // permutation(h, v2 :: (l ++ r)) because
              merge_concat_lemma(h1, r2) &&
                permutation(r, h1 ++ r2) &&
                // permutation(l ++ (r2 ++ h1), l ++ (h1 ++ r2)) because {
                permutation_concat_comm(h1, r2) &&
                permutation_prepend(l, r2 ++ h1, h1 ++ r2) && // }
                // permutation(l ++ (r2 ++ h1), (l ++ r2) ++ h1) because
                permutation_concat_assoc(l, r2, h1) &&
                // permutation(l ++ (h1 ++ r2), (l ++ r2) ++ h1) because
                permutation_tran(l ++ (h1 ++ r2), l ++ (r2 ++ h1), (l ++ r2) ++ h1) &&
                // permutation(r, h1 ++ r2) because
                merge_concat_lemma(h1, r2) &&
                permutation_prepend(l, r, h1 ++ r2) &&
                permutation_tran(l ++ r, l ++ (h1 ++ r2), (l ++ r2) ++ h1) &&
                // permutation(v2 :: (l ++ (h1 ++ r2)), v2 :: (l ++ r2) ++ h1) because
                permutation_cons(l ++ r, (l ++ r2) ++ h1, v2) &&
                permutation_eq(h2 ++ h1, v2 :: (l ++ r2) ++ h1) &&
                permutation_tran(h, v2 :: (l ++ r), v2 :: (l ++ r2) ++ h1) &&
                permutation_tran(h, v2 :: (l ++ r2) ++ h1, h2 ++ h1) &&
                permutation(h2 ++ h1, h1 ++ h2) &&
                permutation_concat_comm(h1, h2) &&
                permutation_tran(h, h2 ++ h1, h1 ++ h2)
            }
        }
      }
    }
  } holds /* verified by Leon */
}