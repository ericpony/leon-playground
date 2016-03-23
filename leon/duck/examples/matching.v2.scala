import duck.collection._
import duck.collection.PairList._
import duck.proof.DistinctOps._
import leon.lang._
import scala.language.{implicitConversions, postfixOps}
import PigeonHolePrinciples._
import PigeonHolePrinciplesLemmas._
import WeightedUndirectedGraph._

object Matching {
  def matching_lemma (graph : Graph) : Unit = {
    // assume that the provided graph has distinct edge weights,
    // and that each edge appears exactly once in the graph representation
    require(distinct(graph.edges.keys) && distinct(graph.edges.values))
    graph.vertices.toList.map(v => graph.minimal_incident_edge_of(v).key)
  } ensuring { res =>
    // there exists at least one matching
    has_collision(res.map(_.dst))
  }
}

object WeightedUndirectedGraph {

  case class Edge (src : BigInt, dst : BigInt)

  case class Graph (edges : PList[Edge, Real]) {

    val vertices = edges.foldRight(Set[BigInt]())((p, s) => s + p.key.src + p.key.dst)

    def is_symmetric : Boolean = {
      edges.forall({
        case Pair(Edge(src, dst), w) =>
          edges.contains(Pair(Edge(dst, src), w))
      })
    }

    def incident_edges_of (vid : BigInt) : PList[Edge, Real] = {
      edges.filter(e => e.key.src == vid || e.key.dst == vid)
    }

    def minimal_incident_edge_of (vid : BigInt) : Pair[Edge, Real] = {
      require(vertices.contains(vid))
      minimal_edge_in(incident_edges_of(vid))
    }

    def neighbors_of (vid : BigInt) : List[BigInt] = {
      require(vertices.contains(vid))
      incident_edges_of(vid).mapList(e => if (e.key.src == vid) e.key.dst else e.key.src)
    }

    def minimal_neighbor_of (vid : BigInt) : BigInt = {
      require(vertices.contains(vid))
      val e = minimal_edge_in(incident_edges_of(vid))
      if (e.key.src == vid) e.key.dst else e.key.src
    }

    def minimal_edge_in (edges : PList[Edge, Real]) : Pair[Edge, Real] = {
      require(!edges.isEmpty)
      val PCons(h, t) = edges
      if (t == PNil()) h
      else {
        val m = minimal_edge_in(t)
        if (m.value >= h.value) h else m
      }
    }
  }
}