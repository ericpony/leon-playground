package duck.spec

import leon.lang._
import AVLTree._
import duck.collection.ListSet._

abstract class IntSet {
  def contains (v: BigInt): Boolean

  def insert (v: BigInt): IntSet

  def delete (v: BigInt): IntSet

  def deleteMax: IntSet

  def deleteMin: IntSet

  def findMax: Option[BigInt]

  def findMin: Option[BigInt]

  def empty: IntSet

  def size: BigInt

  // PROBLEM:
  // Since Leon doesn't support `isInstanceOf` operator,
  // we cannot use implementation-level merge operations
  // (such as heap merge) if we define merge at the ADT level.
  def merge (s: IntSet): IntSet =
    if (s == empty) this
    else insert(s.findMax.get).merge(s.deleteMax)
}

/**
 * An AVLTree-based IntSet
 */
sealed case class TreeSet (tree: TreeNode) extends IntSet {

  def contains (e: BigInt): Boolean = AVLTreeOps(tree).contains(e)

  def insert (e: BigInt): IntSet = TreeSet(AVLTreeOps(tree).insert(e))

  def delete (e: BigInt): IntSet = TreeSet(AVLTreeOps(tree).delete(e))

  def findMax: Option[BigInt] = AVLTreeOps(tree).findMax

  def findMin: Option[BigInt] = AVLTreeOps(tree).findMin

  def deleteMax: IntSet = tree match {
    case Leaf => empty
    case _    => TreeSet(AVLTreeOps(tree).deleteMax._2)
  }

  def deleteMin: IntSet = tree match {
    case Leaf => empty
    case _    => TreeSet(AVLTreeOps(tree).deleteMin._2)
  }

  def size = AVLTreeOps(tree).toList.size

  def empty: IntSet = TreeSet(Leaf)
}