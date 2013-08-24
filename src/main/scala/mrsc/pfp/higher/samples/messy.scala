package mrsc.pfp.higher

import mrsc._
import mrsc.core._
import mrsc.pfp._

object MessyDefs {
  type C = HExpr[Any]
  type Cf = HExpr[HFoldAtom[Any]]
}

import MessyDefs._
import Higher._
import HigherSyntax._

case class HFoldAtom[T](value: Either[HExpr[T], T], safe: Boolean) {
  def isFold = value.isLeft
  def isAtom = value.isRight
  def toExpr = value.fold(x => x, HAtom(_))
  def orSafe(s: Boolean) = HFoldAtom(value, safe || s)
}

object HFoldAtom {
  def apply[T](v: T, s: Boolean = false): HFoldAtom[T] = 
    HFoldAtom(Right(v), s)
  def apply[T](v: HExpr[T], s: Boolean): HFoldAtom[T] = 
    HFoldAtom(Left(v), s)
    
  def isFoldOf[T](c: HExpr[T])(e: Either[Int, HFoldAtom[T]]): Boolean =
    e.fold(_ => false, _.value == Left(c))
  
  def injection[T](c: HExpr[T]): HExpr[HFoldAtom[T]] =
    mapAtom((x:T) => HAtom(HFoldAtom(Right(x), false)))(c)
    
  def expandFoldAtoms[T](c: HExpr[HFoldAtom[T]]): HExpr[T] =
    mapAtom((_:HFoldAtom[T]).toExpr)(c)
    
  def orSafe[T](c: HExpr[HFoldAtom[T]], s: Boolean): HExpr[HFoldAtom[T]] =
    mapVal((_:HFoldAtom[T]).orSafe(s))(c)
}

case class MEdge(
    source: MNode, 
    compose: List[C] => C, 
    dests: List[MNode], 
    silent: Boolean = true, 
    cost: Int = 1) {
  lazy val exprList = {
    val lst = dests.map(_.conf.unchild)
    (compose(lst) :: lst)
  }
  lazy val hash = exprList.hashCode
  // TODO: It is a crutch, we should use first-order data structures instead.
  override def hashCode = hash
  override def equals(o: Any): Boolean = o match {
    case e : MEdge =>
      exprList == e.exprList
    case _ => false
  }
}

class MNode(c: C, d: Int = Int.MaxValue) {
  val conf: C = c
  var depth: Int = d
  val ins = collection.mutable.Set[MEdge]()
  val outs = collection.mutable.Set[MEdge]()
  
  override def hashCode = c.hashCode()
  override def equals(o: Any): Boolean = o match {
    case e : MNode =>
      conf == e.conf
    case _ => false
  }
}

class Messy(supergraph: Boolean = false) extends
	HigherSemantics[Any]
{
  val conf2nodes = collection.mutable.Map[C, MNode]()
  
  var depthBnd = 10//20
  
  def dotLabel(n: MNode): String =
    "\"" + /*n.conf.hashName + "\\l" +*/ n.conf.toString().replaceAllLiterally("\n", "\\l") + "\\l\""
    
  def toDot(): String = {
    val doms = dominators()
    
    def dotStyle(n: MNode): String = {
	    if(successors(n).forall(s => doms(s).contains(n) || !successors(s).contains(n)))
	      ""//"[color=red]"
	    else
	      ""
    }
    
    val nodes = conf2nodes.values.toList.sortBy(_.depth)
    nodes.filter(_.depth != Int.MaxValue).map(n => dotLabel(n) + dotStyle(n) + ";\n").mkString("") ++
    (for(n <- nodes; e <- n.outs; m <- e.dests; if !isVarConst(m.conf)) yield {
      val style = if(e.silent) { if(e.dests.size == 1) "[color=blue]" else "[style=dashed]" } else ""
      dotLabel(n) + " -> " + dotLabel(m) + style + ";\n"
    }).mkString("") 
  }
  
  def addUninitConf(conf: C, parent: C = null): MNode =
    if(supergraph)
      conf2nodes.getOrElseUpdate(HChild(conf, parent), new MNode(HChild(conf, parent)))
    else
      conf2nodes.getOrElseUpdate(conf, new MNode(conf))
    
  def addConf(conf: C, depth: Int = 0): MNode = {
    val n = addUninitConf(conf)
    updateDepth(n, depth)
    return n
  }
 
  def addEdge(e: MEdge) {
    e.source.outs.add(e)
    for(n <- e.dests)
      n.ins.add(e)
    for(n <- e.dests)
      updateDepth(n, e.source.depth + e.cost)
  }
    
  def updateDepth(node: MNode, depth: Int) {
    if(conf2nodes.size > 50000) throw new Exception
    if(node.depth > depth) {
      val olddepth = node.depth
      node.depth = depth
      for(e <- node.outs; n <- e.dests)
        updateDepth(n, depth + e.cost)
      expandNode(node, olddepth)
    }
  }
  
  def genWhistled(n1: MNode, n2: MNode): Boolean = {
    val s = 
      for(g1 <- generalizations(n1.conf); 
		  g2 <- generalizations(n2.conf);
		  if List(g1, sndPart(g1)).exists(c => 
	    	  	containsFix(c) && List(g2, sndPart(g2)).exists(b => equiv(c, b)))) yield true
	//generalize(n2)
	!s.isEmpty
  }
  
  def whistle(node: MNode): Boolean = {
    val whistled = ancestors(node).filter(a => a != node && HHE.he(a.conf, node.conf))
    whistled.filter(genWhistled(node, _)).size >= 2
  }
  
  def expandNode(node: MNode, olddepth: Int = Int.MaxValue) {
    if(supergraph && ancestors(node).exists(n => n.conf.unchild == node.conf.unchild))
      return
      
    if(olddepth >= depthBnd && node.depth < depthBnd) {
      drive(node)
      generalize(node)
      /*if(whistle(node)) {
        //drive(node)
        //generalize(node)
      }
      else {
        if(hsize(node.conf) <= 50)
        	drive(node)
    	generalize(node)
      }*/
    }
  }
  
  def ancestors(node: MNode): List[MNode] = {
    for(e <- node.ins.toList; if e.source.depth < node.depth; a <- e.source :: ancestors(e.source)) yield a
  }
  
  def successors(node: MNode): Set[MNode] = {
    val succ = collection.mutable.Set[MNode]()
    def add(node: MNode) {
      if(!succ.contains(node)) {
        succ.add(node)
	    for(e <- node.outs; n <- e.dests)
	      add(n)
      }
    }
    add(node)
    succ.toSet
  }
  
  def dominators(): Map[MNode, Set[MNode]] = {
    val all = conf2nodes.values.toSet
    forward[Set[MNode]]((o => if(o.depth == 0) Set(o) else all), {case (n,s) => s + n}, {case (a,b) => a.intersect(b)})
  }
  
  def forward[T](outinit: MNode => T, fun: (MNode, T) => T, op: (T,T) => T): Map[MNode, T] = {
    val out = collection.mutable.Map(conf2nodes.values.map(n => (n,outinit(n))).toSeq: _*)
    val in = collection.mutable.Map[MNode, T]()
    var changed = true
    while(changed) {
      changed = false
      for(n <- conf2nodes.values; if n.depth != 0 && n.depth != Int.MaxValue) {
        val l = n.ins.map(e => out(e.source)).toList
        val i = l.tail.fold(l.head)(op)
        val o = fun(n, i)
        in.update(n, i)
        if(out(n) != o) {
          out.update(n, o)
          changed = true
        }
      }
    }
    return out.toMap
  }
  
  def drive(node: MNode) =
    performDriveStep(node, driveStep(node.conf.unchild))
  
  def performDriveStep(node: MNode, ds: DriveStep[C], silent: Boolean = false) {
    ds match {
      case StopDriveStep() =>
      case TransientDriveStep(c) =>
        val cost = 1
        val (f,l) = fixDecomposition((l:List[C]) => l(0), List(c))
        val n = addUninitConf(l(0), node.conf)
        addEdge(new MEdge(node, f, List(n), true, cost))
      case DecomposeDriveStep(comp, l0) =>
        val cost = 1
        val (f,l) = fixDecomposition(comp, l0)
        val ns = l map (addUninitConf(_, node.conf))
        addEdge(new MEdge(node, f, ns, silent, cost))
    }
  }
  
  def sndPart(e: HExpr[Either[C, Any]]) =
	unbound(e).find(_.fold(_ => false, _.isLeft)).get match {
	  case Right(Left(x)) => x 
    }
  
  def generalize(node: MNode) {
    
    //println("generalizing")

    val ddsl =
      for(g <- generalizations(node.conf.unchild).
    		   filter(x => unbound(x).size <= 2).
    		   sortBy(ge => -hsize(ge)*hsize(sndPart(ge))).
    		   take(15)) yield {
        val l = renameUnbound(g) map mapAtom(x => x.fold(y => y, HAtom(_)))
        List((node, DecomposeDriveStep(stdCompose[Any], l)))
      }
    
    //println("done " + ddsl.size + "  total: " + conf2nodes.size)
    ddsl.flatten.map({case (n,d) => performDriveStep(n, d, true)})
  }
  
  def truncate() {
    var changed = false
    for(n <- conf2nodes.values; 
    		if n.depth > 0 && n.depth != Int.MaxValue && containsFix(n.conf.unchild) && n.outs.isEmpty) {
      n.depth = Int.MaxValue
      for(i <- n.ins) {
        for(d <- i.dests if d != n) {
          d.ins.remove(i)
        }
        i.source.outs.remove(i)
      }
      n.ins.clear()
      conf2nodes.remove(n.conf)
      changed = true
    }
    for(n <- conf2nodes.values; 
    		if n.depth > 0 && n.ins.isEmpty) {
      n.depth = Int.MaxValue
      for(o <- n.outs) {
        for(d <- o.dests)
          d.ins.remove(o)
      }
      n.outs.clear()
      conf2nodes.remove(n.conf)
      changed = true
    }
    if(changed)
      truncate()
  }
  
  private def sequence[T](l: List[List[T]]): List[List[T]] = l match {
    case (h :: t) => for(x <- h; y <- sequence(t)) yield x :: y
    case Nil => List(Nil)
  }
  
  def makeFold(c: C): Cf = {
    val myname = HFoldAtom(Left(c), false)
    val unbndargs = unboundList(HFoldAtom.injection(c)).map(fromEither)
    HCall(HAtom(myname), unbndargs)
  }
  
  def makeFix(base: C, c: Cf): Cf = {
    val myname = HFoldAtom(Left(base), true)
    if(unbound(c).contains(Right(myname))) {
      val unbnd = unboundList(HFoldAtom.injection(base)).reverse
	  val corr = unbnd zip (0 to unbnd.size - 1)
	  val corr1 = corr ++ List((Right(myname), unbnd.size))
	  val closed = mapAll((a:Either[Int,HFoldAtom[Any]]) => corr1.toMap.mapValues(HVar(_)).get(a).getOrElse(fromEither(a)))(c)
	  HCall(HFix(hlambdas(closed, corr1.length)), corr.map(_._1.fold(HVar(_), HAtom(_))).reverse)
    }
    else if(unbound(c).contains(Right(HFoldAtom(Left(base), false)))) {
      val injbase = HFoldAtom.injection(base)
      replaceVarAtom(HAtom(HFoldAtom(Left(base), false)), injbase)(c)
    }
    else {
      c
    }
  }
  
  var count = 0
  
  def residuate2(naive: Boolean = false): Map[C, List[C]] = {
    val doms = dominators()
    val succs = conf2nodes.values.map(n => (n, successors(n))).toMap
    val protsets = 
      succs.map({case (n,s) => 
      		(n, s.filter(m =>
      		  succs(m).contains(n) && 
      		  !doms(m).contains(n) && 
      		  !doms(n).contains(m)))}).toMap
      		  
    val done = collection.mutable.Map[MNode, List[Cf]]()
      		  
    def resid(node: MNode, hist: Set[MNode], protect: Set[MNode]): List[Cf] = {
      count += 1
      if(count % 2000 == 0) print(".")
      val d = done.get(node)
      if(hist.contains(node)) {
        List(makeFold(node.conf))
      }
      else if(node.outs.isEmpty) {
        List(HFoldAtom.injection(node.conf))
      }
      else if(d.isDefined && !protect.contains(node)) {
        d.get
      }
      else if(protect.contains(node) || naive) {
        // this node is being processed already
        val unclosed = 
	        (for(e <- node.outs.toList) yield {
	          val children = sequence(e.dests.map(resid(_, hist + node, protect)))
	          children.map(c => HFoldAtom.orSafe(e.compose(c).asInstanceOf[Cf], !e.silent))
	        }).flatten
	        
        unclosed.map(makeFix(node.conf, _)).map(normalize(_)).distinct.sortBy(hsize(_)).take(1)
      }
      else {
        val protect1 = protect ++ protsets(node) + node
        // Instead of doms we can use doms that are successors at the same time
        // (because doms that aren't successors are useless in the history)
        val r = resid(node, doms(node) - node, protect1)
        done.update(node, r)
        r
      }
    }
    
    if(naive) {
      conf2nodes.mapValues(n => if(n.depth == 0) { val r = resid(n, Set(), Set()); r } else Nil).toMap
    }
    else {
	  for(n <- conf2nodes.values; if n.depth == 0)
	    resid(n, Set(), Set())
	    
	  conf2nodes.mapValues(n => done.get(n).map(_.filter(c => true || !unbound(c).exists(_.isRight))).toList.flatten).toMap
    }
  }
  
  def residuate3(): Map[C, List[C]] = {
    val doms = dominators()
    val succs = conf2nodes.values.map(n => (n, successors(n))).toMap
      		  
    val done = collection.mutable.Map[(MNode, Set[MNode]), List[Cf]]()
    
    def resid1(node: MNode, hist: Set[MNode]): List[Cf] = {
      resid(node, hist.intersect(succs(node)))
    }
    
    def resid(node: MNode, hist: Set[MNode]): List[Cf] = {
      count += 1
      if(count % 2000 == 0) print(".")
      val d = done.get((node, hist))
      if(hist.contains(node)) {
        List(makeFold(node.conf))
      }
      else if(node.outs.isEmpty) {
        List(HFoldAtom.injection(node.conf))
      }
      else if(d.isDefined) {
        d.get
      }
      else {
        val unclosed = 
	        (for(e <- node.outs.toList) yield {
	          val children = sequence(e.dests.map(resid1(_, hist + node)))
	          children.map(c => HFoldAtom.orSafe(e.compose(c).asInstanceOf[Cf], !e.silent))
	        }).flatten
	        
        val r = unclosed.map(makeFix(node.conf, _)).map(normalize(_)).distinct.sortBy(hsize(_)).take(1)
        done += Pair(Pair(node, hist), r)
        r
      }
    }
    
	for(n <- conf2nodes.values; if n.depth == 0)
	  resid(n, Set())
	  
	conf2nodes.mapValues(n => done.get(n, doms(n) - n).map(_.filter(c => true || !unbound(c).exists(_.isRight))).toList.flatten).toMap
  }
  
  def residTest(): Map[C, Int] = {
    val doms = dominators()
    val succs = conf2nodes.values.map(n => (n, successors(n))).toMap
      		  
    val done = collection.mutable.Map[(MNode, Set[MNode]), Int]()
    
    def resid1(node: MNode, hist: Set[MNode]): Int = {
      resid(node, hist.intersect(succs(node)))
    }
    
    def resid(node: MNode, hist: Set[MNode]): Int = {
      count += 1
      if(count % 20000 == 0) print(".")
      val d = done.get((node, hist))
      if(hist.contains(node)) {
        1
      }
      else if(node.outs.isEmpty) {
        1
      }
      else if(d.isDefined) {
        d.get
      }
      else {
        val r = 
	        (for(e <- node.outs.toList) yield {
	          e.dests.map(resid1(_, hist + node)).product
	        }).sum
        done += Pair(Pair(node, hist), r)
        r
      }
    }
    
	for(n <- conf2nodes.values; if n.depth == 0)
	  resid(n, Set())
	  
	conf2nodes.mapValues(n => done.get((n, doms(n) - n)).getOrElse(0)).toMap
  }
  
  def levelUp(resid: Map[C, List[C]]) {
    for((conf,s) <- resid; c <- s) {
      val node = conf2nodes(conf)
      val (f,l) = fixDecomposition((l:List[C]) => l(0), List(c))
      val n = addUninitConf(l(0))
      addEdge(new MEdge(node, f, List(n), true, 1))
    }
  }
}

