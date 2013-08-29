package mrsc

import mrsc.core._
import mrsc.pfp._

package object frontend {
  type SG = SGraph[MetaTerm, Label]
  
  def residualize(s: SG): Term = 
    Residuator(Transformations.transpose(s)).result
  
  def peelAbs(t: Term, v: Int = 0): Term = t match {
    case Abs(t1, _) => peelAbs(NamelessSyntax.termSubstTop(FVar(v), t1), v + 1)
    case _ => t
  }
  
  def findEqual(i1: Iterator[Term], i2: Iterator[Term], grsize: Int = 10): Option[(Term, Int)] = {
    val set1 = collection.mutable.Set[Term]()
    val set2 = collection.mutable.Set[Term]()
    
    val j1 = i1.grouped(grsize)
    val j2 = i2.grouped(grsize)
    
    var count = 0
    
    def go(j: Iterator[Seq[Term]], 
           myset: collection.mutable.Set[Term], 
           oset: collection.mutable.Set[Term]): Option[(Term, Int)] = {
      if(j.hasNext && !Thread.interrupted) {
        val n = j.next
        for(t <- n) {
          count += 1
          if(oset.contains(t)) return Some((t, count))
        }
        myset ++= n
      }
      None
    }
    
    while(j1.hasNext || j2.hasNext) {
      go(j1, set1, set2) match { case None => ; case Some(x) => return Some(x) }
      go(j2, set2, set1) match { case None => ; case Some(x) => return Some(x) }
    }
    
    None
  }
  
  def withTimeout[T](f: => T, timeout: Long): T = {
    import java.util.concurrent.{Callable, FutureTask, TimeUnit}
  
    val task = new FutureTask(new Callable[T]() {
      def call() = f
    })
  
    val thread = new Thread(task)
    thread.start()
    
    try {
      task.get(timeout, TimeUnit.SECONDS)
    } catch {
      case t:Throwable =>
        thread.stop()
        throw t
    }
  }
}