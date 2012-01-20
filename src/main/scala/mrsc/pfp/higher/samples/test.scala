package mrsc.pfp.higher.samples

import mrsc._
import mrsc.core._
import mrsc.pfp._
import mrsc.pfp.higher._
import Higher._


object NameGen {
  private val md = java.security.MessageDigest.getInstance("SHA-1")
  private val encoder = new sun.misc.BASE64Encoder()

  def hash(o: Any, n: Int = 9): Name =
    encoder.encode(md.digest(o.toString().getBytes)).take(9)
}

trait HInstanceOfFolding extends PFPRules[HExpr[String]] {
  override def fold(g: G): List[S] =
    g.current.ancestors.find { n =>
      HigherSyntax.findSubst(n.conf, g.current.conf).exists( s => 
        s.forall({case Pair(_,e) => Higher.isVarAtom(e)})
       )
    } map {FoldStep(_)} toList
}

//trait HFindSubstFolding
//	extends PFPRules[Expr] with PFPSyntax[Expr] {
//  
//  def findSubstFunction(from: Expr, to: Expr): Option[Subst[Expr]]
//  
//  override def fold(g: G): List[S] = {
//    // TODO: This is not correct. Should check nonsilentness.
//    val almost_safe_ancestors = 
//      (g.current :: g.current.ancestors).dropWhile( n =>
//    		  n.in != null 
//      )
//    
//    if(almost_safe_ancestors.isEmpty)
//      return List()
//    
//    val safe_ancestors = almost_safe_ancestors.tail 
//    
//    safe_ancestors.find { n =>
//      findSubstFunction(n.conf, g.current.conf).exists( s => 
//        s.forall({case Pair(_,e) => SLLSyntax.isConst(e) || SLLSyntax.isVar(e)})
//       )
//    } map {FoldStep(_)} toList
//  }
//}

object SC extends HigherSemantics[String]
	with PFPRules[HExpr[String]]
	//with MultiResultSCRulesImpl[HExpr[String], DriveInfo[HExpr[String]]]
	with PFPSemantics[HExpr[String]]
	with HInstanceOfFolding {
  
  override def drive(g: G): List[S] =
    List(driveStep(g.current.conf).graphStep)
    
  def supercompile(e: HExpr[String]): List[HExpr[String]] = {
    val gen = GraphGenerator(this, e)
    val graphs = gen.take(10000).toList.map(Transformations.transpose(_))//.distinct
    graphs.map(HigherResiduator("_p" + _.toString()).residuate).map(normalize).distinct
  }
  
  type Warning = List[(N, HExpr[Either[(C,C), String]])]
  def inspect(g: G): Option[Warning] = {
    val gs = g.current.ancestors.map(n => (n, HigherSyntax.generalize(g.current.conf, n.conf)))
    //for(g <- gs) {
    //  println("----")
    //  println(g)
    //}
    val gs1 = gs.filterNot(e => isVarAtom(e._2))
    if(gs1.isEmpty)
      None
    else
      Some(gs1)
  }
  
  def rebuild(signal: Option[Warning], g: G): List[S] = signal match {
    case None => Nil
    case Some(l) =>
      (for((n, e) <- l) yield {
        val withnames = mapVal((e:Either[(C,C), String]) => e.fold(x => Left(("_g" + NameGen.hash(x), x)), Right(_)))(e)
    	
        val unbnd = 
          (for(u <- unbound(withnames).toList) yield u match {
            case Right(Left(t)) => List(t)
            case _ => Nil
          }).flatten
    	
        val fun = mapVal((e:Either[(String, (C,C)), String]) => e.fold((_._1), x => x))(withnames)
    	
        val nmap = (unbnd.map((_._1)) zip (1 to unbnd.length)).toMap  
        val ls = fun :: unbnd.map({case (_,(c,_)) => c})
        val us = fun :: unbnd.map({case (_,(_,c)) => c})
    	
        def f(l: List[HExpr[String]])(n: String): HExpr[String] = nmap.get(n) match {
          case Some(i) => l(i)
          case None => HAtom(n)
        }
        
        val lstep = DecomposeDriveStep((l:List[HExpr[String]]) => mapAtom(f(l))(l.head), ls) 
    	val ustep = DecomposeDriveStep((l:List[HExpr[String]]) => mapAtom(f(l))(l.head), us)
    	
    	//println("====generalization====")
    	//println(fun)
    	//println(g.current.conf)
    	//println(n.conf)
    	
    	
    	List(lstep.graphStep).filterNot(x => HigherSyntax.equiv(fun, g.current.conf)) ++
    	List(UpperStep(n, ustep.graphStep)).
    		filterNot(x => HigherSyntax.equiv(fun, n.conf) || HigherSyntax.equiv(fun, g.current.conf))
      }).flatten
  }
  
  //var nnn = 0
  
  override def steps(g: G): List[S] = fold(g) match {
    case foldSteps if !foldSteps.isEmpty =>
      //println("====folding====")
      //println(foldSteps);
      //println("")
      foldSteps
    case foldSteps =>
      //println(g.current.conf)
      //println(g.incompleteLeaves.mkString("\n", "\n", "\n"))
      val signal = inspect(g)
      val driveSteps = if (signal.isEmpty || g.current.ancestors.length < 20) drive(g) else List()
      val rebuildSteps = rebuild(signal, g)
      //println("===drive steps===")
      //for(ds <- driveSteps)
      //  println(ds)
      //println("============\n\n")
      //nnn += 1
      //if(nnn >= 8)
      //  List(CompleteCurrentNodeStep[HExpr[String], DriveInfo[HExpr[String]]]())
      //else
      rebuildSteps ++ driveSteps
  }
}

object Test  {

  var stepCounter = 0
  var yCounter = 0
  
  def printCounters() {
    println(yCounter + "/" + stepCounter)
    stepCounter = 0
    yCounter = 0
  }
  
  def evaluate[T](e: HExpr[T]): HExpr[T] = {
    //println(e)
    stepCounter += 1;
    decompose(e) match {
      case (_, HFix(_)) => yCounter += 1;
      case _ =>
    }
    
    object sem extends HigherSemantics[T] { override val doNormalization = true }
    sem.driveStep(e) match {
      case DecomposeDriveStep(f, l) => f(l map evaluate)
      case StopDriveStep() => e
      case TransientDriveStep(x) => evaluate(x)
    }
  }
  
  
  
  def main(args: Array[String]):Unit = {
    def p = HigherParsers.parseExpr _
    def addp(n: String, s: String) {
      val e = mapAtom(HigherGlobals.getByName)(p(s))
      HigherGlobals.add(n, e)
    }
    
    addp("add", "Y \\ f x y -> case x of { S x -> S (f x y); Z -> y; }")
    addp("mul", "Y \\ f x y -> case x of { S x -> add y (f x y); Z -> Z; }")
	//val add = p("\\a b -> (Y \\ f x y -> case x of { S x -> S (f x y); Z -> y; }) b a")
	//val add = p("Y \\ f x -> case x of { S x -> S (f x); Z -> Z; }")
    
    val expr = HigherGlobals.getByName("mul")
    
	def test(h: HExpr[String]) {
      val d = HCall(h, List(p("S (S (Z))"), p("S (S (S (Z)))")))
      //val d = HCall(h, List(p("S (Z)")))
      println(evaluate(d))
      printCounters()
      println("")
    }
	
    println(expr)
	test(expr)
	
	val sc = SC.supercompile(expr)
	for(s1 <- sc) {
	  val s = normalize(s1)
	  println(s)
	  test(s)
	}
  }

}