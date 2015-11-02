package duck.spec

import duck.collection._
import duck.proof.sugar._
import leon.lang._
import leon.annotation._

/** The red-black tree implementation used for TreeMaps and TreeSets in Scala.
  * Simplified and rewritten in PureScala by ericpony.
  *
  * Source:
  * https://github.com/scala/scala/blob/2.12.x/src/library/scala/collection/immutable/RedBlackTree.scala
  */
object RedBlackTree {

  sealed abstract class Tree {
    val black: Tree
    val red: Tree
    val isRed: Boolean
    val isBlack: Boolean
    val left: Tree
    val right: Tree
    val count: BigInt
    val key: BigInt
    val value: BigInt
  }

  case object Empty extends Tree {
    override val black = Empty
    override val red = Empty
    override val left = Empty
    override val right = Empty
    override val key = BigInt(0)
    override val value = BigInt(0)
    override val count = BigInt(0)
    override val isRed = false
    override val isBlack = false
  }

  case class RedTree (override val key: BigInt,
                      override val value: BigInt,
                      override val left: Tree,
                      override val right: Tree) extends Tree {
    override val count = 1 + left.count + right.count
    override val black: Tree = BlackTree(key, value, left, right)
    override val red: Tree = this
    override val isRed = true
    override val isBlack = false
  }

  case class BlackTree (override val key: BigInt,
                        override val value: BigInt,
                        override val left: Tree,
                        override val right: Tree) extends Tree {
    override val count = 1 + left.count + right.count
    override val black: Tree = this
    override val red: Tree = RedTree(key, value, left, right)
    override val isRed = false
    override val isBlack = true
  }

  def contains (tree: Tree, x: BigInt): Boolean = lookup(tree, x) != Empty

  def get (tree: Tree, x: BigInt): Option[BigInt] = {
    val t = lookup(tree, x)
    if (t == Empty) None[BigInt]()
    else Some(t.value)
  }


  def lookup (tree: Tree, x: BigInt): Tree = {
    if (tree == Empty) tree
    else {
      if (x < tree.key) lookup(tree.left, x)
      else if (x > tree.key) lookup(tree.right, x)
      else tree
    }
  }

  def count (tree: Tree): BigInt = tree.count

  def update (tree: Tree, k: BigInt, v: BigInt, overwrite: Boolean): Tree = blacken(upd(tree, k, v, overwrite))

  def delete (tree: Tree, k: BigInt): Tree = blacken(del(tree, k))

  def smallest (tree: Tree): Tree = {
    if (tree.left == Empty)
      tree
    else
      smallest(tree.left)
  }

  def greatest (tree: Tree): Tree = {
    if (tree.right == Empty)
      tree
    else
      greatest(tree.right)
  }


  def nth (tree: Tree, n: BigInt): Tree = {
    val count = tree.left.count
    if (n < count)
      nth(tree.left, n)
    else if (n > count)
      nth(tree.right, n - count - 1)
    else
      tree
  }

  def blacken (t: Tree): Tree = if (t == Empty) Empty else t.black

  def mkTree (isBlack: Boolean, k: BigInt, v: BigInt, l: Tree, r: Tree): Tree =
    if (isBlack) BlackTree(k, v, l, r) else RedTree(k, v, l, r)

  def balanceLeft (isBlack: Boolean, z: BigInt, zv: BigInt, l: Tree, d: Tree): Tree = if (l == Empty) Empty
  else {
    if (l.isRed && l.left.isRed) {
      RedTree(l.key, l.value, BlackTree(l.left.key, l.left.value, l.left.left, l.left.right), BlackTree(z, zv, l.right, d))
    } else if (l.isRed && l.right.isRed) {
      RedTree(l.right.key, l.right.value, BlackTree(l.key, l.value, l.left, l.right.left), BlackTree(z, zv, l.right.right, d))
    } else
      mkTree(isBlack, z, zv, l, d)
  }

  def balanceRight (isBlack: Boolean, x: BigInt, xv: BigInt, a: Tree, r: Tree): Tree = if (r == Empty) Empty
  else {
    if (r.isRed && r.left.isRed)
      RedTree(r.left.key, r.left.value, BlackTree(x, xv, a, r.left.left), BlackTree(r.key, r.value, r.left.right, r.right))
    else if (r.isRed && r.right.isRed)
      RedTree(r.key, r.value, BlackTree(x, xv, a, r.left), BlackTree(r.right.key, r.right.value, r.right.left, r.right.right))
    else
      mkTree(isBlack, x, xv, a, r)
  }

  def upd (tree: Tree, k: BigInt, v: BigInt, overwrite: Boolean): Tree = if (tree == Empty) {
    RedTree(k, v, Empty, Empty)
  } else {
    if (k < tree.key) balanceLeft(tree.isBlack, tree.key, tree.value, upd(tree.left, k, v, overwrite), tree.right)
    else if (k > tree.key) balanceRight(tree.isBlack, tree.key, tree.value, tree.left, upd(tree.right, k, v, overwrite))
    else if (overwrite || k != tree.key) mkTree(tree.isBlack, k, v, tree.left, tree.right)
    else tree
  }

  def updNth (tree: Tree, idx: BigInt, k: BigInt, v: BigInt, overwrite: Boolean): Tree = if (tree == Empty) {
    RedTree(k, v, Empty, Empty)
  } else {
    val rank = tree.left.count + 1
    if (idx < rank) balanceLeft(tree.isBlack, tree.key, tree.value, updNth(tree.left, idx, k, v, overwrite), tree.right)
    else if (idx > rank) balanceRight(tree.isBlack, tree.key, tree.value, tree.left, updNth(tree.right, idx - rank, k, v, overwrite))
    else if (overwrite) mkTree(tree.isBlack, k, v, tree.left, tree.right)
    else tree
  }

  /* Based on Stefan Kahrs' Haskell version of Okasaki's Red&Black Trees
   * Constructing Red-Black Trees, Ralf Hinze: http://www.cs.ox.ac.uk/ralf.hinze/publications/WAAAPL99b.ps.gz
   * Red-Black Trees in a Functional Setting, Chris Okasaki: https://wiki.rice.edu/confluence/download/attachments/2761212/Okasaki-Red-Black.pdf */
  def del (tree: Tree, k: BigInt): Tree = if (tree == Empty) Empty
  else {
    def balance (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = if (tl.isRed) {
      if (tr.isRed) {
        RedTree(x, xv, tl.black, tr.black)
      } else if (tl.left.isRed) {
        RedTree(tl.key, tl.value, tl.left.black, BlackTree(x, xv, tl.right, tr))
      } else if (tl.right.isRed) {
        RedTree(tl.right.key, tl.right.value, BlackTree(tl.key, tl.value, tl.left, tl.right.left), BlackTree(x, xv, tl.right.right, tr))
      } else {
        BlackTree(x, xv, tl, tr)
      }
    } else if (tr.isRed) {
      if (tr.right.isRed) {
        RedTree(tr.key, tr.value, BlackTree(x, xv, tl, tr.left), tr.right.black)
      } else if (tr.left.isRed) {
        RedTree(tr.left.key, tr.left.value, BlackTree(x, xv, tl, tr.left.left), BlackTree(tr.key, tr.value, tr.left.right, tr.right))
      } else {
        BlackTree(x, xv, tl, tr)
      }
    } else {
      BlackTree(x, xv, tl, tr)
    }
    def subl (t: Tree) = t.red

    def balLeft (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = {
      if (tl.isRed) {
        RedTree(x, xv, tl.black, tr)
      } else if (tr.isBlack) {
        balance(x, xv, tl, tr.red)
      } else if (tr.isRed && tr.left.isBlack) {
        RedTree(tr.left.key, tr.left.value, BlackTree(x, xv, tl, tr.left.left), balance(tr.key, tr.value, tr.left.right, subl(tr.right)))
      } else {
        // sys.error("Defect: invariance violation")
        Empty
      }
    }

    def balRight (x: BigInt, xv: BigInt, tl: Tree, tr: Tree): Tree = {
      if (tr.isRed) {
        RedTree(x, xv, tl, tr.black)
      } else if (tl.isBlack) {
        balance(x, xv, tl.red, tr)
      } else if (tl.isRed && tl.right.isBlack) {
        RedTree(tl.right.key, tl.right.value, balance(tl.key, tl.value, subl(tl.left), tl.right.left), BlackTree(x, xv, tl.right.right, tr))
      } else {
        // sys.error("Defect: invariance violation")
        Empty
      }
    }

    def delLeft = {
      if (tree.left.isBlack)
        balLeft(tree.key, tree.value, del(tree.left, k), tree.right)
      else
        RedTree(tree.key, tree.value, del(tree.left, k), tree.right)
    }

    def delRight = {
      if (tree.right.isBlack)
        balRight(tree.key, tree.value, tree.left, del(tree.right, k))
      else
        RedTree(tree.key, tree.value, tree.left, del(tree.right, k))
    }

    def append (tl: Tree, tr: Tree): Tree = if (tl == Empty) {
      tr
    } else if (tr == Empty) {
      tl
    } else if (tl.isRed && tr.isRed) {
      val bc = append(tl.right, tr.left)
      if (bc.isRed) {
        RedTree(bc.key, bc.value, RedTree(tl.key, tl.value, tl.left, bc.left), RedTree(tr.key, tr.value, bc.right, tr.right))
      } else {
        RedTree(tl.key, tl.value, tl.left, RedTree(tr.key, tr.value, bc, tr.right))
      }
    } else if (tl.isBlack && tr.isBlack) {
      val bc = append(tl.right, tr.left)
      if (bc.isRed) {
        RedTree(bc.key, bc.value, BlackTree(tl.key, tl.value, tl.left, bc.left), BlackTree(tr.key, tr.value, bc.right, tr.right))
      } else {
        balLeft(tl.key, tl.value, tl.left, BlackTree(tr.key, tr.value, bc, tr.right))
      }
    } else if (tr.isRed) {
      RedTree(tr.key, tr.value, append(tl, tr.left), tr.right)
    } else if (tl.isRed) {
      RedTree(tl.key, tl.value, tl.left, append(tl.right, tr))
    } else {
      // sys.error("unmatched tree on append: " + tl + ", " + tr)
      Empty
    }
    if (k < tree.key) delLeft
    else if (k > tree.key) delRight
    else append(tree.left, tree.right)
  }

  /**
   * Unzip left tree on the rightmost side and right tree on the leftmost side until one is
   * found to be deeper, or the bottom is reached
   */
  def unzipBoth (left: Tree,
                 right: Tree,
                 leftZipper: List[Tree],
                 rightZipper: List[Tree],
                 smallerDepth: BigInt): (List[Tree], Boolean, Boolean, BigInt) = {
    // Once a side is found to be deeper, unzip it to the bottom
    def unzip (zipper: List[Tree], leftMost: Boolean): List[Tree] = {
      require(zipper != Nil[Tree]())
      val next = if (leftMost) zipper.head.left else zipper.head.right
      if (next == Empty) zipper
      else unzip(Cons(next, zipper), leftMost)
    } ensuring {
      res => res != Nil[Tree]()
    }

    if (left.isBlack && right.isBlack) {
      unzipBoth(left.right, right.left, Cons(left, leftZipper), Cons(right, rightZipper), smallerDepth + 1)
    } else if (left.isRed && right.isRed) {
      unzipBoth(left.right, right.left, Cons(left, leftZipper), Cons(right, rightZipper), smallerDepth)
    } else if (right.isRed) {
      unzipBoth(left, right.left, leftZipper, Cons(right, rightZipper), smallerDepth)
    } else if (left.isRed) {
      unzipBoth(left.right, right, Cons(left, leftZipper), rightZipper, smallerDepth)
    } else if ((left == Empty) && (right == Empty)) {
      (Nil[Tree](), true, false, smallerDepth)
    } else if ((left == Empty) && right.isBlack) {
      val leftMost = true
      (unzip(Cons(right, rightZipper), leftMost), false, leftMost, smallerDepth)
    } else if (left.isBlack && (right == Empty)) {
      val leftMost = false
      (unzip(Cons(left, leftZipper), leftMost), false, leftMost, smallerDepth)
    } else {
      // sys.error("unmatched trees in unzip: " + left + ", " + right)
      (Nil[Tree](), true, false, BigInt(0))
    }
  } ensuring { res =>
    !res._2 implies res._1 != Nil[Tree]()
  }

  /**
   * Returns the zipper for the side with deepest black nodes depth, a flag
   * indicating whether the trees were unbalanced at all, and a flag indicating
   * whether the zipper was traversed left-most or right-most.
   *
   * The zipper returned might have been traversed left-most (always the left child)
   * or right-most (always the right child). Left trees are traversed right-most,
   * and right trees are traversed leftmost.
   *
   * If the trees were balanced, returns an empty zipper.
   */
  def compareDepth (left: Tree, right: Tree): (List[Tree], Boolean, Boolean, BigInt) = {
    unzipBoth(left, right, Nil[Tree](), Nil[Tree](), 0)
  } ensuring { res =>
    val zipper = res._1
    val levelled = res._2
    val leftMost = res._3
    val depth = res._4
    if (!levelled) {
      countBlack(zipper) >= depth && depth >= 1
    } else true
  }

  def countBlack (zipper: List[Tree]): BigInt = {
    if (zipper == Nil[Tree]()) 0
    else if (zipper.head.isBlack) 1 + countBlack(zipper.tail)
    else countBlack(zipper.tail)
  }

  // remove n-1 black nodes from zipper
  def findDepth (zipper: List[Tree], depth: BigInt): List[Tree] = {
    require(countBlack(zipper) >= depth && depth > 0)
    if (!zipper.head.isBlack)
      findDepth(zipper.tail, depth)
    else if (depth == 1)
      zipper
    else
      findDepth(zipper.tail, depth - 1)
  } ensuring {
    res => res != Nil[Tree]()
  }

  def rebalance (tree: Tree, newLeft: Tree, newRight: Tree) = {
    // Blackening the smaller tree avoids balancing problems on union;
    // this can't be done later, though, or it would change the result of compareDepth
    val blkNewLeft = blacken(newLeft)
    val blkNewRight = blacken(newRight)
    val (zipper, levelled, leftMost, smallerDepth) = compareDepth(blkNewLeft, blkNewRight)

    if (levelled) {
      BlackTree(tree.key, tree.value, blkNewLeft, blkNewRight)
    } else {
      // pre-cond: 1 <= smallerDepth <= zipper.size
      val zipFrom = findDepth(zipper, smallerDepth)
      val union: Tree = if (leftMost) {
        RedTree(tree.key, tree.value, blkNewLeft, zipFrom.head)
      } else {
        RedTree(tree.key, tree.value, zipFrom.head, blkNewRight)
      }
      val zippedTree = zipFrom.tail.foldLeft(union) { (tree, node) =>
        if (leftMost)
          balanceLeft(node.isBlack, node.key, node.value, tree, node.right)
        else
          balanceRight(node.isBlack, node.key, node.value, node.left, tree)
      }
      zippedTree
    }
  }
}