package mrsc.core

import scala.collection.mutable.Queue
import scala.collection.mutable.ListBuffer

trait GraphRewriteRules[C, D] {
  type N = SNode[C, D]
  type G = SGraph[C, D]
  type S = GraphRewriteStep[C, D]
  def steps(g: G): List[S]
}

sealed trait GraphRewriteStep[C, D] { val original: AnyRef = Unit }
case class CompleteCurrentNodeStep[C, D](override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]
case class AddChildNodesStep[C, D](ns: List[(C, D)], override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]
case class FoldStep[C, D](to: SPath, override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]
case class RebuildStep[C, D](c: C, override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]
case class RollbackStep[C, D](to: SPath, c: C, override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]
case class EmptyStep[C, D](override val original: AnyRef = Unit) extends GraphRewriteStep[C, D]

class GraphGenerator[C, D](val rules: GraphRewriteRules[C, D], val conf: C, val withHistory: Boolean = false)
  extends Iterator[SGraph[C, D]] {

  protected var completeGs: Queue[SGraph[C, D]] = Queue()
  protected var pendingGs: List[SGraph[C, D]] = List(initial(conf))

  protected def initial(c: C): SGraph[C, D] = {
    val initialNode = SNode[C, D](c, null, None, Nil)
    SGraph(List(initialNode), Nil, Nil)
  }

  protected def normalize(): Unit =
    while (completeGs.isEmpty && !pendingGs.isEmpty) {
      val pendingDelta = ListBuffer[SGraph[C, D]]()
      val g = pendingGs.head
      val rewrittenGs = rules.steps(g) map { GraphGenerator.executeStep(_, g, withHistory) }
      for (g1 <- rewrittenGs)
        if (g1.isComplete) {
          completeGs.enqueue(g1)
        } else {
          pendingDelta += g1
        }
      pendingGs = pendingDelta ++: pendingGs.tail
    }

  def hasNext: Boolean = {
    normalize()
    !completeGs.isEmpty
  }

  def next(): SGraph[C, D] = {
    if (!hasNext) throw new NoSuchElementException("no graph")
    completeGs.dequeue()
  }
}

object GraphGenerator {
  def apply[C, D](rules: GraphRewriteRules[C, D], conf: C, withHistory: Boolean = false) =
    new GraphGenerator[C,D](rules, conf, withHistory)
  
  def executeStep[C, D](step: GraphRewriteStep[C, D], g: SGraph[C, D], withHistory: Boolean = false): SGraph[C, D] = {
    val prev = if (withHistory) Some(g) else None 
    step match {
      case AddChildNodesStep(List(), _) =>
        executeStep(CompleteCurrentNodeStep(), g, withHistory)
      case CompleteCurrentNodeStep(_) =>
        SGraph(g.incompleteLeaves.tail, g.current :: g.completeLeaves, g.current :: g.completeNodes, prev)
      case AddChildNodesStep(ns, _) =>
        val deltaLeaves: List[SNode[C, D]] = ns.zipWithIndex map {
          case ((conf, dInfo), i) =>
            val in = SEdge(g.current, dInfo)
            SNode(conf, in, None, i :: g.current.sPath)
        }
        SGraph(deltaLeaves ++ g.incompleteLeaves.tail, g.completeLeaves, g.current :: g.completeNodes, prev)
      case FoldStep(basePath, _) =>
        val node = g.current.copy(base = Some(basePath))
        SGraph(g.incompleteLeaves.tail, node :: g.completeLeaves, node :: g.completeNodes, prev)
      case RebuildStep(c, _) =>
        val node = g.current.copy(conf = c)
        SGraph(node :: g.incompleteLeaves.tail, g.completeLeaves, g.completeNodes, prev)
      case EmptyStep(_) =>
        g
      case RollbackStep(sPath, c, _) =>
        // it is possible to optimize this part
        // if we keep history, then we can to find a graph
        // where a node to rollback is a current node
        val to = g.current.ancestors.find(_.sPath == sPath).get
        def prune_?(n: SNode[C, D]) = n.tPath.startsWith(to.tPath)
        val node = to.copy(conf = c)
        val completeNodes1 = g.completeNodes.filterNot(prune_?)
        val completeLeaves1 = g.completeLeaves.filterNot(prune_?)
        val incompleteLeaves1 = g.incompleteLeaves.tail.filterNot(prune_?)
        SGraph(node :: incompleteLeaves1, completeLeaves1, completeNodes1, prev)
    }
  }
}