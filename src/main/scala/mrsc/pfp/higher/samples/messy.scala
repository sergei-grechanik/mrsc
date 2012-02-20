package mrsc.pfp.higher

import mrsc._
import mrsc.core._
import mrsc.pfp._

object MessyDefs {
  type C = HExpr[String]
}

import MessyDefs._
import Higher._
import HigherSyntax._

case class MEdge(
    source: MNode, 
    compose: List[C] => C, 
    dests: List[MNode], 
    silent: Boolean = true, 
    cost: Int = 1) {
  lazy val exprList = {
    val lst = dests.map(_.conf)
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

class Messy extends
	HigherSemantics[String]
{
  val conf2nodes = collection.mutable.Map[C, MNode]()
  val supercompiled = collection.mutable.Map[MNode, Set[C]]()
  val residuated = collection.mutable.Map[MNode, List[C]]()
  
  var depthBnd = 10
  
  def dotLabel(n: MNode): String =
    "\"" + n.conf.hashName + "\\l" + n.conf.toString().replaceAllLiterally("\n", "\\l") + "\\l\""
    
  def toDot(): String = {
    val doms = dominators()
    
    def dotStyle(n: MNode): String = {
	    if(successors(n).forall(s => doms(s).contains(n) || !successors(s).contains(n)))
	      "[color=red]"
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
  
  def addUninitConf(conf: C): MNode = 
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
    if(conf2nodes.size > 10000) throw new Exception
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
    val whistled = /*ancestors(node)*/conf2nodes.values.filter(a => a != node && HHE.he(a.conf, node.conf))
    whistled.filter(genWhistled(node, _)).size >= 2
  }
  
  def expandNode(node: MNode, olddepth: Int = Int.MaxValue) {
    if(olddepth >= depthBnd && node.depth < depthBnd) {
      if(whistle(node)) {
        //drive(node)
        //generalize(node)
      }
      else {
        if(hsize(node.conf) <= 40)
        	drive(node)
    	generalize(node)
      }
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
    performDriveStep(node, driveStep(node.conf))
  
  def performDriveStep(node: MNode, ds: DriveStep[C], silent: Boolean = false) {
    ds match {
      case StopDriveStep() =>
      case TransientDriveStep(c) =>
        val cost = 1
        val (f,l) = fixDecomposition((l:List[C]) => l(0), List(c))
        val n = addUninitConf(l(0))
        addEdge(new MEdge(node, f, List(n), true, cost))
      case DecomposeDriveStep(comp, l0) =>
        val cost = 1
        val (f,l) = fixDecomposition(comp, l0)
        val ns = l map addUninitConf
        addEdge(new MEdge(node, f, ns, silent, cost))
    }
  }
  
  def sndPart(e: HExpr[Either[HExpr[String], String]]) =
	unbound(e).find(_.fold(_ => false, _.isLeft)).get match {
	  case Right(Left(x)) => x 
    }
  
  def generalize(node: MNode) {
    
    println("generalizing")

    val ddsl =
      for(g <- generalizations(node.conf).
    		   filter(x => unbound(x).size <= 2).
    		   sortBy(ge => -hsize(ge)*hsize(sndPart(ge))).
    		   take(15)) yield {
        val l = renameUnbound(g) map mapAtom(x => x.fold(y => y, HAtom(_)))
        List((node, DecomposeDriveStep(stdCompose[String], l)))
      }
    
    println("done " + ddsl.size + "  total: " + conf2nodes.size)
    ddsl.flatten.map({case (n,d) => performDriveStep(n, d, true)})
  }
  
  def truncate() {
    var changed = false
    for(n <- conf2nodes.values; 
    		if n.depth > 0 && n.depth != Int.MaxValue && containsFix(n.conf) && n.outs.isEmpty) {
      n.depth = Int.MaxValue
      for(i <- n.ins)
        i.source.outs.remove(i)
      n.ins.clear()
      changed = true
    }
    if(changed)
      truncate()
  }
  
  private def sequence[T](l: List[List[T]]): List[List[T]] = l match {
    case (h :: t) => for(x <- h; y <- sequence(t)) yield x :: y
    case Nil => List(Nil)
  }
  
  def residuate(conf: C): List[C] =
    residuate(conf2nodes(conf)).filter(c => !unbound(c).exists(_.isRight))
  
  def residuate(node: MNode, history: List[(Boolean, MNode)] = Nil): List[C] = {
    if(history.size > depthBnd)
      return List()
      
    val myname = "_f" + node.conf.hashName
    val unbndargs = unboundList(node.conf).map(fromEither)
    val safehist = history.dropWhile(_._1 == true) 
    if(safehist.exists(_._2 == node) || (!safehist.isEmpty && safehist(0)._2.depth >= node.depth)) {
      List(HCall(HAtom(myname), unbndargs))
    }
    else if(node.outs.isEmpty)  {
      List(node.conf)
    }
    else {
      val already = residuated.get(node)
      if(already.isDefined)
        return already.get
      
      val all =
      (for(e <- node.outs) yield {
        val children = sequence(e.dests.map(residuate(_, (e.silent, node) :: history).toList))
        for(l <- children) yield {
          if(l.exists(c => unbound(c).contains(Right(myname)))) {
        	  val expr = e.compose(l)
        	  val unbnd = unboundList(node.conf).reverse
	          val corr = unbnd zip (0 to unbnd.size - 1)
	          val corr1 = corr ++ List((Right(myname), unbnd.size))
	          val closed = mapAll((a:Either[Int,String]) => corr1.toMap.mapValues(HVar(_)).get(a).getOrElse(fromEither(a)))(expr)
	          normalize(HCall(HFix(hlambdas(closed, corr1.length)), corr.map(_._1.fold(HVar(_), HAtom(_))).reverse))
          }
          else {
            normalize(e.compose(l))
          }
        }
      }).flatten.toList.distinct.sortBy(hsize(_))
      
      val count = Math.max(1, 10*(depthBnd - node.depth)/depthBnd)
      
      val best = all//.take(count)
      println(all.size)
      val newlevel = all.filter(nontrivialCall).filter(c => !unbound(c).exists(_.isRight))
      
      residuated.update(node, best)
      
      val bestclosed = newlevel.take(count)
      val before = supercompiled.getOrElse(node, Set())
      supercompiled.update(node, (before ++ bestclosed).toList.sortBy(hsize(_)).take(count).toSet)  
      
      best
    }
  }
  
  def makeFold(c: C): C = {
    val myname = "_f" + c.hashName
    val unbndargs = unboundList(c).map(fromEither)
    HCall(HAtom(myname), unbndargs)
  }
  
  def makeFix(base: C, c: C): C = {
    // TODO: We should control correctness here
    // I think we should mark each occurrence of a reference to this node
    // with the silentness of the path to it
    val myname = "_f" + base.hashName
    if(unbound(c).contains(Right(myname))) {
      val unbnd = unboundList(base).reverse
	  val corr = unbnd zip (0 to unbnd.size - 1)
	  val corr1 = corr ++ List((Right(myname), unbnd.size))
	  val closed = mapAll((a:Either[Int,String]) => corr1.toMap.mapValues(HVar(_)).get(a).getOrElse(fromEither(a)))(c)
	  HCall(HFix(hlambdas(closed, corr1.length)), corr.map(_._1.fold(HVar(_), HAtom(_))).reverse)
    }
    else
      c
  }
  
  def residuate2(naive: Boolean = false): Map[C, List[C]] = {
    val doms = dominators()
    val succs = conf2nodes.values.map(n => (n, successors(n))).toMap
    val protsets = 
      succs.map({case (n,s) => 
      		(n, s.filter(m =>
      		  succs(m).contains(n) && 
      		  !doms(m).contains(n) && 
      		  !doms(n).contains(m)))}).toMap
      		  
    val done = collection.mutable.Map[MNode, List[C]]()
      		  
    def resid(node: MNode, hist: Set[MNode], protect: Set[MNode]): List[C] = {
      val d = done.get(node)
      if(hist.contains(node)) {
        List(makeFold(node.conf))
      }
      else if(node.outs.isEmpty) {
        List(node.conf)
      }
      else if(d.isDefined && !protect.contains(node)) {
        d.get
      }
      else if(protect.contains(node) || naive) {
        // this node is being processed already
        val unclosed = 
	        (for(e <- node.outs.toList) yield {
	          val children = sequence(e.dests.map(resid(_, hist + node, protect)))
	          children.map(e.compose(_))
	        }).flatten
	        
        unclosed.map(makeFix(node.conf, _)).map(normalize(_)).distinct.sortBy(hsize(_)).take(15)
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
      conf2nodes.mapValues(n => if(n.depth == 0) resid(n, Set(), Set()) else Nil).toMap
    }
    else {
	  for(n <- conf2nodes.values; if n.depth == 0)
	    resid(n, Set(), Set())
	    
	  conf2nodes.mapValues(n => done.get(n).map(_.filter(c => !unbound(c).exists(_.isRight))).toList.flatten).toMap
    }
  }
  
  def levelUp() {
    for((node,s) <- supercompiled; c <- s) {
      val (f,l) = fixDecomposition((l:List[C]) => l(0), List(c))
      val n = addUninitConf(l(0))
      addEdge(new MEdge(node, f, List(n), true, 1))
    }
    supercompiled.clear()
  }
}

