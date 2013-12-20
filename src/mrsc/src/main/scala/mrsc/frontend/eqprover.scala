package mrsc.frontend

import mrsc.core._
import mrsc.pfp._
import NamelessSyntax._

import scala.collection.mutable.Queue
import scala.collection.mutable.ListBuffer

class EqProvingGG(
    rules1: GraphRewriteRules[MetaTerm, Label], conf1: MetaTerm, 
    rules2: GraphRewriteRules[MetaTerm, Label], conf2: MetaTerm,
    withHistory: Boolean = false)
  extends Iterator[(SGraph[MetaTerm, Label], SGraph[MetaTerm, Label])] {

  type C = MetaTerm
  type D = Label
  type S = GraphRewriteStep[C, D]
  type G = SGraph[C,D]
  type P = (G, G)
  
  protected var completeGs: Queue[P] = Queue()
  protected var pendingGs: List[P] = List((initial(conf1), initial(conf2)))

  protected def initial(c: C): SGraph[C, D] = {
    val initialNode = SNode[C, D](c, null, None, Nil)
    SGraph(List(initialNode), Nil, Nil)
  }

  protected def normalize(): Unit =
    while (completeGs.isEmpty && !pendingGs.isEmpty) {
      val pendingDelta = ListBuffer[P]()
      val (g1, g2) = pendingGs.head
      val ps = stepPairs(g1, g2)
      //println("res: " + ps.size)
      val rewrittenGs = 
        ps map { case (s1,s2) => 
            (GraphGenerator.executeStep(s1, g1, withHistory),
             GraphGenerator.executeStep(s2, g2, withHistory)) }
      for ((g1,g2) <- rewrittenGs)
        if (g1.isComplete && g2.isComplete) {
          completeGs.enqueue((g1, g2))
        } else {
          pendingDelta += ((g1, g2))
        }
      pendingGs = pendingDelta ++: pendingGs.tail
    }
  
  def stepPairs(g1: G, g2: G): List[(S, S)] = {
    if(!g1.isComplete && !g2.isComplete && subclass.equiv(g1.current.conf, g2.current.conf)) {
      //println("eq: " + NamedSyntax.named(g1.current.conf.asInstanceOf[Term]))
      return List((CompleteCurrentNodeStep(), CompleteCurrentNodeStep()))
    }
    
    val ss1 = if(g1.isComplete) List(EmptyStep():S) else rules1.steps(g1)
    val ss2 = if(g2.isComplete) List(EmptyStep():S) else rules2.steps(g2)
    
    //println("ss1: " + ss1)
    //println("ss2: " + ss2 + "\n")
    
    val sss: List[List[(S, S)]] =
      for(s1 <- ss1; s2 <- ss2) yield {
        //println("s1: " + s1)
        //println("s2: " + s2 + "\n")
        
        val res =
        (s1.original, s2.original) match {
          case (TransientMStep(_), TransientMStep(_)) =>
            List((s1,s2))
          case (TransientMStep(_), UnfoldMStep(_)) =>
            List((s1,s2))
          case (UnfoldMStep(_), TransientMStep(_)) =>
            List((s1,s2))
          case (UnfoldMStep(_), UnfoldMStep(_)) =>
            List((s1,s2))
          case (TransientMStep(_), _) =>
            List((s1, EmptyStep(): S))
          case (UnfoldMStep(_), _) => 
            List((s1, EmptyStep(): S))
          case (_, TransientMStep(_)) =>
            List((EmptyStep(): S, s2))
          case (_, UnfoldMStep(_)) => 
            List((EmptyStep(): S, s2))
          case (StopMStep, StopMStep) =>
            List((s1,s2))
          case (RebuildMStep(rb1), RebuildMStep(rb2)) =>
            List((s1,s2))
            
          case (DecomposeCtrMStep(c1), DecomposeCtrMStep(c2)) => 
            if(c1.name == c2.name) List((s1,s2))
            else return Nil
          case (DecomposeAbsMStep(_, _), DecomposeAbsMStep(_, _)) =>
            List((s1,s2))
          case (DecomposeVarApp(_, _), DecomposeVarApp(_, _)) =>
            List((s1,s2))
          case (VariantsMStep(_, cs1), VariantsMStep(_, cs2)) =>
            if(cs1.map(_._1.name) == cs2.map(_._1.name)) List((s1,s2))
            else return Nil
          case (o1: MStep, o2: MStep) if o1.isDefining && o2.isDefining =>
            return Nil
            
          case (DecomposeRebuildingMStep(t1), DecomposeRebuildingMStep(t2)) 
                if s1.asInstanceOf[AddChildNodesStep[C,D]].ns.size == 
                   s2.asInstanceOf[AddChildNodesStep[C,D]].ns.size => 
            List((s1,s2))
          case (FreezeRebuildingMStep(t1), FreezeRebuildingMStep(t2)) 
                if s1.asInstanceOf[AddChildNodesStep[C,D]].ns.size == 
                   s2.asInstanceOf[AddChildNodesStep[C,D]].ns.size => 
            List((s1,s2))
            
          case (o1: MStep, o2: MStep) =>
            List()
            
          case _ => //one of the args is Unit
            (s1,s2) match {
              case (CompleteCurrentNodeStep(_), CompleteCurrentNodeStep(_)) =>
                List((s1,s2))
              case (FoldStep(_, _), FoldStep(_, _)) =>
                List((s1,s2))
              case (RebuildStep(_, _), RebuildStep(_, _)) =>
                List((s1,s2))
              case (RollbackStep(_, _, _), RollbackStep(_, _, _)) =>
                List((s1,s2))
              case (AddChildNodesStep(ns1, o1: MStep), AddChildNodesStep(ns2, o2: MStep)) 
                    if ns1.size == ns2.size =>
                List((s1,s2))
              case (EmptyStep(_),_) =>
                List((s1,s2))
              case (_,EmptyStep(_)) =>
                List((s1,s2))
              case _ =>
                List()
            }   
        }
        
        //println("res: " + res.size + "\n")
        
        res
      }
    
    sss.flatten
  }

  def hasNext: Boolean = {
    normalize()
    !completeGs.isEmpty
  }

  def next(): P = {
    if (!hasNext) throw new NoSuchElementException("no graph")
    completeGs.dequeue()
  }
}