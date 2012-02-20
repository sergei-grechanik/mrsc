package mrsc.core

case class SuperGraphGenerator[C, D](rules: GraphRewriteRules[C, D], conf: C) {

  lazy val sgraph: SGraph[C, D] = {
    val initialNode = SNode[C, D](conf, null, None, Nil)
    var g = SGraph(List(initialNode), Nil, Nil)
    
    while(g.current != null) {
      val cur = g.current
      val steps = rules.steps(g)
      for(s <- steps) {
        SuperGraphGenerator.executeStep(s, g) match {
          case SGraph(inc, comL, comN) =>
            g = SGraph(cur :: inc, comL, comN)
        }
      }
      g match {
      	case SGraph(inc, comL, comN) =>
      	  if(steps.isEmpty)
      	    g = SGraph(inc.remove(l => l == cur), cur :: comL, cur :: comN)
      	  else
      		g = SGraph(inc.remove(l => l == cur), comL, comN)
      }
    }
    
    g
  }
  
  lazy val tgraph = Transformations.transpose(sgraph)

}

object SuperGraphGenerator {
  def executeStep[C, D](step: GraphRewriteStep[C, D], g: SGraph[C, D]): SGraph[C, D] = step match {
    case CompleteCurrentNodeStep() =>
      SGraph(g.incompleteLeaves.tail, g.current :: g.completeLeaves, g.current :: g.completeNodes)
    case AddChildNodesStep(ns) =>
      val allNodes = (g.incompleteLeaves ++ g.completeNodes)
      val siblings = allNodes.filter(n => !n.sPath.isEmpty && n.sPath.tail == g.current.sPath).toSet
      val sibCount = siblings.size
      // We presume that ns nodes have equal driveinfos.
      if(!ns.isEmpty && !siblings.exists(_.in.driveInfo == ns.head._2)) {
        val deltaLeaves: List[SNode[C, D]] = ns.zipWithIndex map {
          case ((conf, dInfo), i) =>
            val in = SEdge(g.current, dInfo)
            SNode(conf, in, None, (i + sibCount) :: g.current.sPath)
        }
        SGraph(deltaLeaves ++ g.incompleteLeaves.tail, g.completeLeaves, g.current :: g.completeNodes)
      } else
        SGraph(g.incompleteLeaves.tail, g.completeLeaves, g.current :: g.completeNodes)
    case FoldStep(baseNode) =>
      val node = g.current.copy(base = Some(baseNode.sPath), baseNode = baseNode)
      SGraph(g.incompleteLeaves.tail, node :: g.completeLeaves, node :: g.completeNodes)
    case RebuildStep(c) =>
      val node = g.current.copy(conf = c)
      SGraph(node :: g.incompleteLeaves.tail, g.completeLeaves, g.completeNodes)
    case RollbackStep(to, c) =>
      executeStep(UpperStep(to, RebuildStep(c)), g)
    case UpperStep(to, s) =>
      val graph = SGraph(to :: g.incompleteLeaves.tail, g.completeLeaves, g.incompleteLeaves.head :: g.completeNodes)
      executeStep(s, graph)
    case RewriteThenFoldStep(c, di, baseNode) =>
      executeStep(FoldStep(baseNode), executeStep(AddChildNodesStep(List((c,di))), g))
  }
  
  def sgraph2dot[C, D](g: SGraph[C, D]): String = {
    var done: Set[SNode[C,D]] = Set()
    var dot: String = ""
    
    def label(n: SNode[C,D]): String =
      "\"" + n.hashCode() + " " + (if(n.ancestors.isEmpty) "" else n.in.driveInfo.hashCode()) + "\\l" + 
      			n.conf.toString().replaceAllLiterally("\n", "\\l") + "\\l\""
      
    def proc(n: SNode[C,D], inc: Boolean = false) {
      if(!done.contains(n)) {
        done += n
        if(!n.ancestors.isEmpty) {
          dot = label(n.ancestors.head) + " -> " + label(n) + ";\n" + dot
          if(inc)
            dot += label(n) + " [color=red];\n"
          proc(n.ancestors.head, inc)
        }
        if(n.base.isDefined)
          dot = label(n) + " -> " + label(n.baseNode) + " [color=blue];\n" + dot
      }
    }
    
    for(l <- g.completeLeaves) proc(l)
    for(l <- g.incompleteLeaves) proc(l, true)
    
    dot
  }
  
  def tgraph2dot[C, D](g: TGraph[C, D]): String = {
    var dot = ""
    
    def label(n: TNode[C,D]): String =
      "\"" + n.hashCode() + "\\l" + 
      			n.conf.toString().replaceAllLiterally("\n", "\\l") + "\\l\""
      
    def proc(n: TNode[C,D], inc: Boolean = false) {
      for(e <- n.outs if e.node.base.isDefined || !e.node.outs.isEmpty || true) {
        val style = if(n.outs.filter(_.driveInfo == e.driveInfo).length == 1) "[color=red]" else ""
        dot += label(n) + " -> " + label(e.node) + style + ";\n"
        proc(e.node)
      }
      
      if(n.base.isDefined)
        dot += label(n) + " -> " + label(g.get(n.base.get)) + " [color=blue];\n"
    }
    
    proc(g.root)
    
    dot
  }
  
  def super2list[C, D](g: TGraph[C, D]): List[TGraph[C, D]] = {
    def node2list(n: TNode[C,D], shiftlist: TPath = List()): List[TGraph[C,D]] = {
      def shift(p: TPath) = p.zip(shiftlist).map({case (a,b) => a - b})
      val shiftedbase = n.base.map(shift)
      val shiftedpath = shift(n.tPath)
      if(n.outs.isEmpty) {
        val node: TNode[C,D] = TNode(n.conf, Nil, shiftedbase, shiftedpath)
        List(TGraph(node, List(node)))
      }
      else
	      (n.outs.groupBy(_.driveInfo) map { case (di,es) =>
	        val shiftlist1 = shiftlist ++ List(es.head.node.sPath.head)
	        val subgraphs = sequence(es map (e => node2list(e.node, shiftlist1)))
	        subgraphs map { gs =>
	          val outs1 = gs map {g => TEdge(g.root, di)}
	          val node = TNode(n.conf, outs1, shiftedbase, shiftedpath)
	          TGraph(node, gs.map(_.leaves).flatten)
	        }
	      }).flatten.toList
    }
    node2list(g.root)
  }
  
  private def sequence[T](l: List[List[T]]): List[List[T]] = l match {
    case (h :: t) => for(x <- h; y <- sequence(t)) yield x :: y
    case Nil => List(Nil)
  }
}