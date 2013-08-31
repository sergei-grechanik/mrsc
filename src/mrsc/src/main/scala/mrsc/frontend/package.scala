package mrsc

import mrsc.core._
import mrsc.pfp._
import scalaz.IsEmpty
import java.util.concurrent.TimeoutException

package object frontend {
  type SG = SGraph[MetaTerm, Label]
  
  def residualize(s: SG): Term =
    Residuator(Transformations.transpose(s)).result
  
  def peelAbs(t: Term, v: Int = 0): (Term, Int) = t match {
    case Abs(t1, _) => peelAbs(NamelessSyntax.termSubstTop(FVar(v), t1), v + 1)
    case _ => (t, v)
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
      if(j.hasNext) {
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
  
  def findReturning(i: Iterator[Term], constr: String): Option[(Term, Int)] = {
    var count = 0
    
    for(t <- i) {
      count += 1
      possibleCtrs(peelAbs(t)._1) match {
        case Some(s) if s == Set(constr) => return Some((t, count))
        case _ =>
      }
    }
    
    None
  }
  
  def possibleCtrs(t: Term, bvars: Map[Int, Option[Set[String]]] = Map(),
      apps: List[Option[Set[String]]] = Nil): Option[Set[String]] = {
    lazy val shifted = bvars.map(p => (p._1 + 1, p._2))
    val res =
    t match {
      case BVar(i, _) => bvars.getOrElse(i, None)
      case FVar(_, _) => None
      case GVar(n, _) => None
      case Abs(body, _) => 
        // Here we treat (\x -> C ...) like just C
        if(apps.isEmpty) possibleCtrs(body, shifted)
        else possibleCtrs(body, shifted + (0 -> apps(0)), apps.tail)
      case App(t1, t2, _) =>
        possibleCtrs(t1, bvars, possibleCtrs(t2, bvars) :: apps)
      case Let(v, in, _) =>
        val vro = possibleCtrs(v, bvars)
        possibleCtrs(in, shifted + (0 -> vro), apps)
      case Fix(body, _) =>
        var curset: Option[Set[String]] = Some(Set())
        var stop = false
        while(!stop) {
          val newset = possibleCtrs(body, shifted + (0 -> curset), apps)
          if(newset == curset) stop = true
          else curset = newset
        }
        curset
      case Ctr(name, args, _) =>
        Some(Set(name))
      case Case(sel, branches, _) =>
        val selctrs = possibleCtrs(sel, bvars)
        branches.collect {
          case (pat, body) if selctrs.isEmpty || selctrs.get(pat.name) =>
            val shifted = bvars.map(p => (p._1 + pat.args.size, p._2))
            possibleCtrs(body, shifted, apps)
        }.reduce( (a,b) => for(s1 <- a; s2 <- b) yield s1 | s2 )
    }
    //println(t + "\nbvars: " + bvars + "\napp: " + apps + "\n" + res + "\n")
    res
  }
  
  def withTimeout[T](f: => T, timeout: Long): T = {
    if(timeout != 0) {
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
    } else
      f
  }
}