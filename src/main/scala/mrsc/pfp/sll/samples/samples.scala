package mrsc.pfp.sll.samples

import mrsc.core._
import mrsc.pfp._
import mrsc.pfp.sll._

trait FindSubstBySC {
  val program: Program
  val supercompiler = new SC7(program, HEByCouplingWithRedexWhistle)
  
  var cachedResiduals: Map[Expr, List[Expr]] = Map()
  var cachedSubsts: Map[Pair[Expr, Expr], Option[Subst[Expr]]] = Map()
  
  def supercompile(e: Expr): List[Expr] = {
    cachedResiduals.get(e) match {
      case Some(l) => l
      case None =>
        val gen = GraphGenerator(supercompiler, e)
        val i = for(g <- gen if g.isComplete)
        			yield SLLResiduator().residuate(Transformations.transpose(g))
        val l = i.take(1000).toList.distinct
        cachedResiduals += Pair(e, l)
        
        //println("\nsupercompiled " + e + "\n" + l.length + "\n")
        
        return l
    }
  }
  
  def findSubstFunction(from: Expr, to: Expr): Option[Subst[Expr]] = {
    cachedSubsts.get((from, to)) match {
      case Some(s) =>
        //println("\n" + from + "\n" + to + "\n" + s + "\n")
        s
      case None =>
        SLLSyntax.findSubst(from, to) match {
          case Some(s) =>
            cachedSubsts += Pair((from,to), Some(s))
            return Some(s)
          case _ =>
        }
        
        val sfrom = supercompile(from)
        val sto = supercompile(to)
        val i = 
      		for(f <- sfrom.iterator; t <- sto.iterator; val s = SLLSyntax.findSubst(f, t); if s.isDefined)
  		      yield (f, t, s.get)
  		      
  		if(i.isEmpty) {
  		  cachedSubsts += Pair((from,to), None)
  		  return None
  		}
	    else {
	      val (f, t, sub) = i.next()
	      cachedSubsts += Pair((from,to), Some(sub))
	      println("\n" + from + "\n" + to + "\n" + f + "\n" + t + "\n" + sub + "\n")
	      return Some(sub)
	    }
    }
  }
}

trait TwoLevelSC extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with FindSubstBySC
  with FindSubstFolding
  with BinaryWhistle[Expr]

// MultiDoubleAllBinaryGens
class SCTwo(val program: Program, val ordering: PartialOrdering[Expr])
  extends TwoLevelSC
  with DoubleAllBinaryGensOnBinaryWhistle[Expr]

trait SC extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with InstanceOfFolding
  with BinaryWhistle[Expr]

trait SCEx extends MultiResultSCRulesExperimental[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with InstanceOfFolding
  with BinaryWhistle[Expr]

// ClassicCurrentGen
class SC1(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with LowerMsgOrDrivingOnBinaryWhistle[Expr]

class SC1Ex(val program: Program, val ordering: PartialOrdering[Expr])
  extends SCEx
  with LowerMsgOrDrivingOnBinaryWhistle[Expr]

// MultiDoubleMsg
class SC2(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with DoubleMsgOnBinaryWhistle[Expr]

class SC2Ex(val program: Program, val ordering: PartialOrdering[Expr])
  extends SCEx
  with DoubleMsgOnBinaryWhistle[Expr]

// MultiUpperAllBinaryGens
class SC3(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with UpperAllBinaryGensOnBinaryWhistle[Expr]

// MultiUpperAllBinaryGensOrDrive
class SC4(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with UpperAllBinaryGensOrDriveOnBinaryWhistle[Expr]

// MultiLowerAllBinaryGens
class SC5(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with LowerAllBinaryGensOnBinaryWhistle[Expr]

// MultiLowerAllBinaryGensOrDrive
class SC6(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with LowerAllBinaryGensOrDriveOnBinaryWhistle[Expr]

// MultiDoubleAllBinaryGens
class SC7(val program: Program, val ordering: PartialOrdering[Expr])
  extends SC
  with DoubleAllBinaryGensOnBinaryWhistle[Expr]

class MultiAllRebuildings(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with Folding[Expr]
  with BinaryWhistle[Expr]
  with AllRebuildings[Expr]

class MultiLowerRebuildings(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with Folding[Expr]
  with BinaryWhistle[Expr]
  with LowerRebuildingsOnBinaryWhistle[Expr]

class MultiUpperRebuildings(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with Folding[Expr]
  with BinaryWhistle[Expr]
  with UpperRebuildingsOnBinaryWhistle[Expr]

class MultiDoubleRebuildingsOnWhistle(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with InstanceOfFolding
  with BinaryWhistle[Expr]
  with DoubleRebuildingsOnBinaryWhistle[Expr]

class MultiDoubleRebuildingsOnWhistleEx(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesExperimental[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with InstanceOfFolding
  with BinaryWhistle[Expr]
  with DoubleRebuildingsOnBinaryWhistle[Expr]

class ClassicDangerousGen(val program: Program, val ordering: PartialOrdering[Expr])
  extends MultiResultSCRulesImpl[Expr, DriveInfo[Expr]]
  with SLLSyntax
  with SLLSemantics
  with Driving[Expr]
  with Folding[Expr]
  with BinaryWhistle[Expr]
  with LowerMsgOrUpperMggOnBinaryWhistle[Expr]


object Samples {
  //type Machine1 = Machine[Expr, DriveInfo[Expr], Extra[Expr]]

  def multi1(w: PartialOrdering[Expr])(p: Program) = new MultiAllRebuildings(p, w)
  def multi2(w: PartialOrdering[Expr])(p: Program) = new MultiLowerRebuildings(p, w)
  def multi3(w: PartialOrdering[Expr])(p: Program) = new MultiUpperRebuildings(p, w)
  def multi4(w: PartialOrdering[Expr])(p: Program) = new MultiDoubleRebuildingsOnWhistle(p, w)
  def classic1(w: PartialOrdering[Expr])(p: Program) = new ClassicDangerousGen(p, w)
  def classic2(w: PartialOrdering[Expr])(p: Program) = new SC1(p, w)
  def classic3(w: PartialOrdering[Expr])(p: Program) = new SC3(p, w)

  private def expand(n: Int, s: String): String = {
    val init = " " * n
    val tmp = s + init
    tmp take n
  }

  private def expandRight(n: Int, s: String): String = {
    val init = " " * n
    val tmp = init + s
    tmp takeRight n
  }

  private def residuateAndCheck(gen: GraphGenerator[Expr, DriveInfo[Expr]], task: SLLTask): Unit = {
    for (g <- gen if g.isComplete) {
      val t = Transformations.transpose(g)
      println(t)
      val res = SLLResiduator().residuate(t)
      println(res)
      Checker.check(task, Lifting.expr2Task(res))
    }
  }
  
  private def residuate(gen: GraphGenerator[Expr, DriveInfo[Expr]], task: SLLTask): Unit = {
    for (g <- gen if g.isComplete) {
      val t = Transformations.transpose(g)
      val (expr,defs) = Lifting.lift(SLLResiduator().residuate(t))
      println(expr)
      for(d <- defs)
        println(d)
      println("")
    }
  }

  // just tries classic variants of 
  // SLL supercompilation
  def showResidualPrograms(task: SLLTask): Unit = {

    println("************************")
    println(task.target)
    println("************************")
    println()

    {
      println("**classic+ up:**")
      val m1 = classic1(HEByCouplingWhistle)(task.program)
      residuateAndCheck(new GraphGenerator(m1, task.target), task)
    }

    {
      println("**classic+ down:**")
      val m2 = classic2(HEByCouplingWhistle)(task.program)
      residuateAndCheck(new GraphGenerator(m2, task.target), task)

    }

    println("**others:**")

    {
      val m3 = classic3(HEByCouplingWhistle)(task.program)
      residuateAndCheck(new GraphGenerator(m3, task.target), task)
    }

    {
      val m3 = classic3(HEByCouplingWithRedexWhistle)(task.program)
      residuateAndCheck(new GraphGenerator(m3, task.target), task)
    }

    println()
  }

  def showResidualProgramsForTasks(): Unit = {

    showResidualPrograms(SLLTasks.namedTasks("NaiveFib"))
    showResidualPrograms(SLLTasks.namedTasks("FastFib"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlus"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlusa"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlusb"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlusc"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlus1"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlus1a"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlus1b"))
    showResidualPrograms(SLLTasks.namedTasks("EqPlus1c"))
    showResidualPrograms(SLLTasks.namedTasks("OddEven"))
    showResidualPrograms(SLLTasks.namedTasks("EvenMult"))
    showResidualPrograms(SLLTasks.namedTasks("EvenSqr"))
    showResidualPrograms(SLLTasks.namedTasks("NaiveReverse"))
    showResidualPrograms(SLLTasks.namedTasks("FastReverse"))
    showResidualPrograms(SLLTasks.namedTasks("LastDouble"))
    showResidualPrograms(SLLTasks.namedTasks("App"))
    showResidualPrograms(SLLTasks.namedTasks("Idle"))

  }

  // count graphs
  def count(gen: GraphGenerator[_, _], limit: Integer = 1800): (Integer, Integer) = {
    var completed = 0
    var unworkable = 0
    for (g <- gen) {
      if (g.isComplete) {
        completed += 1
      } else {
        unworkable += 1
      }
      if (completed + unworkable > limit) {
        return (-1, -1)
      }
    }
    (completed, unworkable)
  }
  
  // count residual programs and graphs
  def countResidual(
      name: String,
      task: SLLTask,
      gen: GraphGenerator[Expr, DriveInfo[Expr]], 
      subf: (Expr, Expr) => Option[Subst[Expr]] = SLLSyntax.findSubst): 
    	  (Integer, Integer) = {
    val graphs = gen.take(1000).toList.map(Transformations.transpose(_)).distinct
    val progs = graphs.map(SLLResiduator(subf).residuate(_)).distinct
    
      //println("")
      //println(graphs(0))
      //println("")
    //var n = 0;
    //for(p <- graphs) {
    //  val out = new java.io.FileWriter("residual" + n)
    //  out.write(p.toString())
    //  out.close 
    //  n += 1
    //} 
    
    var n = 0;
    for(p <- progs) {
      val tsk = Lifting.expr2Task(p)
      val out = new java.io.FileWriter("residual-" + name + "-"  + n)
      out.write(tsk.toString())
      out.close
      n += 1
      Checker.check(task, tsk)
    }
    
    /*for(g <- gen) {
      val tree = Transformations.transpose(g)
      val p = SLLResiduator(subf).residuate2(tree)
      val tsk = Lifting.expr2Task(p)
      Checker.check(task, tsk)
    }*/
    
    return (progs.length, graphs.length)
  }

  def countGraphs(task: SLLTask): Unit = {
    val info = expand(40, task.target.toString)
    print(info)

    val sctwo = new SCTwo(task.program, HEByCouplingWithRedexWhistle)
    
    val machines = List(
        (new SC7(task.program, HEByCouplingWithRedexWhistle), "1"),
        (sctwo, "2")
      //new SC1(task.program, HEByCouplingWithRedexWhistle),
      //new SC1Ex(task.program, HEByCouplingWithRedexWhistle))
      //new MultiDoubleRebuildingsOnWhistle(task.program, HEWhistle),
      //new MultiDoubleRebuildingsOnWhistleEx(task.program, HEWhistle))
      //new MultiAllRebuildingsEx(task.program, HEWhistle))
      //HEByCouplingWhistle
      )
      
    machines foreach { case Pair(m, name) =>
      val gen = GraphGenerator(m, task.target)
      val (ps, gs) = countResidual(name, task, gen, sctwo.findSubstFunction)
      val res = expandRight(12, ps + "/" + gs)
      print(res)
      
      m match {
        case r : MultiResultSCRulesExperimental[Expr, DriveInfo[Expr]] =>
          println("")
          for(b <- r.bases)
            println(b)
          println("")
          r.bases = Set()
        case _ =>
      }
      
      //residuate(gen, task)
    }

    println()
  }

  def countGraphsForTasks(): Unit = {
    println("Counting completed graphs")
    println()
    val header = expand(40, """Task \ Supercompiler""") + expandRight(12, "1") +
      expandRight(12, "2") + expandRight(12, "3")
    println(header)
    println()

    countGraphs(SLLTasks.namedTasks("EvenDouble"))
    /*countGraphs(SLLTasks.namedTasks("NaiveFib"))
    //countGraphs(SLLTasks.namedTasks("FastFib"))
    countGraphs(SLLTasks.namedTasks("EqPlus"))
    countGraphs(SLLTasks.namedTasks("EqPlusa"))
    countGraphs(SLLTasks.namedTasks("EqPlusb"))
    countGraphs(SLLTasks.namedTasks("EqPlusc"))
    countGraphs(SLLTasks.namedTasks("EqPlus1"))
    countGraphs(SLLTasks.namedTasks("EqPlus1a"))
    countGraphs(SLLTasks.namedTasks("EqPlus1b"))
    countGraphs(SLLTasks.namedTasks("EqPlus1c"))
    countGraphs(SLLTasks.namedTasks("OddEven"))
    countGraphs(SLLTasks.namedTasks("EvenMult"))
    countGraphs(SLLTasks.namedTasks("EvenSqr"))
    countGraphs(SLLTasks.namedTasks("NaiveReverse"))
    countGraphs(SLLTasks.namedTasks("FastReverse"))
    countGraphs(SLLTasks.namedTasks("LastDouble"))
    countGraphs(SLLTasks.namedTasks("App"))
    countGraphs(SLLTasks.namedTasks("Idle"))
    countGraphs(SLLTasks.namedTasks("Ololo"))*/
    //countGraphs(SLLTasks.namedTasks("KMP"))
    //countGraphs(SLLTask("gEven(gMult(S(S(S(Z()))), n))", SLLTasks.peanoProgram))

    //countGraphs(SLLTasks.namedTasks("EvenMult"))
    
    println()
    println("1 - classic")
    println("2 - branch when folding with nontrivial substitution")
    //println("1 - classic msg mix, he by coupling")
    //println("2 - all gens (up and down by whistle), he")
    //println("3 - always gen, he")

    println()
    println()
  }

  def main(args: Array[String]): Unit = {

    // 85726 completed graphs here:
    //preRun(SLLTasks.namedTasks("FastFib"))

    // 0 results here (because only UP generalization is allowed)
    // runTask(SLLTasks.namedTasks("FastFib"), multi3(HEByCouplingWhistle)_)

    countGraphsForTasks()

    //showResidualProgramsForTasks()

  }

}