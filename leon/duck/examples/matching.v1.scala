import duck.collection._
import duck.collection.PairList._
import duck.proof.DistinctOps._
import leon.lang._
import scala.language.{implicitConversions, postfixOps}
import PigeonHolePrinciples._
import PigeonHolePrinciplesLemmas._

object Matching {

  case class Edge (src : BigInt, dst : BigInt)

  case class Graph (edges : PList[Edge, Real])

  def matching_lemma (graph : Graph) : Unit = {
    require(is_symmetric(graph) && has_distinct_weights(graph))
    vertices_of(graph.edges).toList.map(
      v => minimal_incident_edge_of(v, graph.edges).key
    )
  } ensuring { res =>
    // there exists at least one matching
    res.exists({
      case e1 => {
        val rest = res.removeFirst(e1)
        val e2 = Edge(e1.dst, e1.src)
        rest.contains(e1) || rest.contains(e2)
      }
    })
  }

  def is_symmetric (graph : Graph) : Boolean = {
    graph.edges.forall({
      case Pair(Edge(src, dst), w) =>
        graph.edges.contains(Pair(Edge(dst, src), w))
    })
  }
  def has_distinct_weights (graph : Graph) : Boolean = {
    distinct(graph.edges.values)
  }

  def vertices_of (edges : PList[Edge, Real]) = {
    edges.foldRight(Set[BigInt]())((p, s) => s + p.key.src + p.key.dst)
  }

  def incident_edges_of (vertex : BigInt, edges : PList[Edge, Real]) : PList[Edge, Real] = {
    require(vertices_of(edges) contains vertex)
    edges.filter(e => e.key.src == vertex || e.key.dst == vertex)
  }

  def neighbors_of (vertex : BigInt, edges : PList[Edge, Real]) : List[BigInt] = {
    require(vertices_of(edges) contains vertex)
    incident_edges_of(vertex, edges).mapList(e => if (e.key.src == vertex) e.key.dst else e.key.src)
  }

  def minimal_neighbor_of (vertex : BigInt, edges : PList[Edge, Real]) : BigInt = {
    require(vertices_of(edges) contains vertex)
    val e = minimal_edge_in(incident_edges_of(vertex, edges))
    if (e.key.src == vertex) e.key.dst else e.key.src
  }

  def minimal_incident_edge_of (vertex : BigInt, edges : PList[Edge, Real]) : Pair[Edge, Real] = {
    require(vertices_of(edges) contains vertex)
    minimal_edge_in(incident_edges_of(vertex, edges))
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
