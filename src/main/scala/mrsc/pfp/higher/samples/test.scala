package mrsc.pfp.higher.samples

import mrsc._
import mrsc.core._
import mrsc.pfp._
import mrsc.pfp.higher._
import Higher._
import HigherSyntax._

trait HInstanceOfFolding extends PFPRules[HExpr[String]] {
  def findSubstFunction(from: HExpr[String], to: HExpr[String]): Option[HSubst[String]] = 
    HigherSyntax.findSubst(from, to)
  
  override def fold(g: G): List[S] = {
    val almost_safe_ancestors = 
      (g.current :: g.current.ancestors).dropWhile( n =>
    		  n.in != null && n.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]]
      )
    
    if(almost_safe_ancestors.isEmpty)
      return List()
    
    val safe_ancestors = almost_safe_ancestors.tail
    
    safe_ancestors.find { n =>
      findSubstFunction(n.conf, g.current.conf).exists( s => 
        s.forall({case Pair(_,e) => Higher.isVarAtom(e)})
       )
    } map {FoldStep(_)} toList 
  //map (n => 
  //    RewriteThenFoldStep(n.conf, DecomposeStepInfo((l:List[HExpr[String]]) => subst(l(0), findSubstFunction(n.conf, g.current.conf).get)), n)) toList
  }
}

case class SC extends HigherSemantics[String]
	with PFPRules[HExpr[String]]
	//with MultiResultSCRulesImpl[HExpr[String], DriveInfo[HExpr[String]]]
	with PFPSemantics[HExpr[String]]
	with HInstanceOfFolding {
  
  override def drive(g: G): List[S] =
    List(driveStep(g.current.conf).graphStep)
  
  type Warning = List[(N, HExpr[Either[(C,C), String]])]
  def inspect(g: G): Option[Warning] = {
    val gs = g.current.ancestors.map(n => (n, HigherSyntax.generalize(g.current.conf, n.conf)))
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
        val unbnd = 
          (for(u <- unboundList(e)) yield u match {
            case Right(Left(p)) => List(p)
            case _ => Nil
          }).flatten
    	
        val shift = unbnd.length
          
        val fun = mapAtom(
        			(e:Either[(C,C), String]) => e.fold(p => HVar(unbnd.indexOf(p)), a => HAtom(a)))(
        			    mapVar(i => HVar(i + shift))(e))
        
        val nmap = (unbnd.map((_._1)) zip (1 to unbnd.length)).toMap  
        val ls = fun :: unbnd.map({case (c,_) => c})
        val us = fun :: unbnd.map({case (_,c) => c})
    	
        def f(l: List[HExpr[String]])(n: Int): HExpr[String] = 
          if(n >= shift) 
            HVar(n - shift)
          else
            l(n + 1)
        
        val lstep = DecomposeDriveStep((l:List[HExpr[String]]) => mapVar(f(l))(l.head), ls) 
    	val ustep = DecomposeDriveStep((l:List[HExpr[String]]) => mapVar(f(l))(l.head), us)
    	
    	List(lstep.graphStep).filterNot(x => HigherSyntax.equiv(fun, g.current.conf)) ++
    	List(UpperStep(n, ustep.graphStep)).
    		filterNot(x => HigherSyntax.equiv(fun, n.conf) || HigherSyntax.equiv(fun, g.current.conf))
      }).flatten
  }
  
  //var nnn = 0
  var out = new java.io.FileWriter("allgraph.dot")

  def nodeName(n: N): String =
    "\"" + (if(n.ancestors.isEmpty) "" else n.ancestors.head.conf.hashCode() + "\\l") + n.conf.toString().replaceAllLiterally("\n", "\\l") + "\\l\""
  
  def drawStep(cur: N, s: S, style: String = ""): Unit = s match {
    case FoldStep(base) =>
      out.write(nodeName(cur) + " -> " + nodeName(base) + style + ";\n")
    case AddChildNodesStep(ns) =>
      //out.write(nodeName(cur) + " -> " + "\"" + cur.hashCode() + "\\l" + ns.hashCode() + "\"" + ";\n")
      for (n <- ns)
        //out.write("\"" + cur.hashCode() + "\\l" + ns.hashCode() + "\"" + " -> " + "\"" + (cur :: cur.ancestors).hashCode() + "\\l" + n._1.toString().replaceAllLiterally("\n", "\\l") + "\\l\"" + style + ";\n")
        out.write(nodeName(cur) + " -> " + "\"" + (cur.conf /*:: cur.ancestors*/).hashCode() + "\\l" + n._1.toString().replaceAllLiterally("\n", "\\l") + "\\l\"" + style + ";\n")
    case UpperStep(to, s) =>
      drawStep(to, s, style)
    case _ =>
  }
  
  override def steps(g: G): List[S] = fold(g) match {
    case foldSteps if !foldSteps.isEmpty =>
//      out.write("// fold\n")
//      foldSteps map (drawStep(g.current, _, "[color=blue]"))
//      out.flush()
      
      foldSteps
    case foldSteps =>
      val signal = inspect(g)
      val rebuildSteps = rebuild(signal, g)
      val driveSteps = if (rebuildSteps.isEmpty || g.current.ancestors.length < 10) drive(g) else List()
      
      print((g.completeNodes.size + g.incompleteLeaves.size) + " ")
      
//      out.write("// rebuild\n")
//      rebuildSteps map (drawStep(g.current, _, "[style=dashed]"))
//      out.write("// drive " + g.current.ancestors.length + "\n")
//      driveSteps map (drawStep(g.current, _, "[color=red]"))
//      out.flush()
      
      driveSteps ++ rebuildSteps
  }
}

case class SCTwo(baseSC: HExpr[String] => Set[HExpr[String]])
	extends SC with Memos {
  
  val mySC = mutableHashMapMemo.apply((x:HExpr[String]) =>
    baseSC(x).toList.sortBy(hsize(_)).take(10)
    )
  
  override def steps(g: G): List[S] = fold(g) match {
    case foldSteps if !foldSteps.isEmpty =>
      foldSteps
    case foldSteps =>
      val signal = inspect(g)
      val rebuildSteps = rebuild(signal, g)
      val driveSteps = if (rebuildSteps.isEmpty || g.current.ancestors.length < 10) drive(g) else List()
      
      val superSteps = 
        if((g.current.in == null || !g.current.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]]) && 
            g.current.ancestors.length < 10)
          mySC(g.current.conf).
          	filter(hsize(_) < hsize((g.current :: g.current.ancestors).last.conf)).
          	filter(!HigherSyntax.equiv(_, g.current.conf)).
          	take(1).map(TransientDriveStep(_).graphStep)
        else
          Nil
    
//      val sig1 =
//	      for(n <- g.current.ancestors; 
//			  x <- mySC(g.current.conf);
//			  y <- mySC(n.conf);
//			  ge = HigherSyntax.generalize(x,y);
//			  if !isVarAtom(ge))
//	        yield (n,ge)
//      
//	  val superSteps = rebuild(Some(sig1), g).filter(_.isInstanceOf[UpperStep[C,DriveInfo[C]]])
	        
      println(superSteps.length)
      
      //if(superSteps.isEmpty || hsize(superSteps.head.ns.head._1) > hsize(g.current.conf))
        driveSteps ++ rebuildSteps ++ superSteps
      //else
      //  superSteps
  }
}

object HSupecompilers extends Memos {
  type C = HExpr[String]
  type D = DriveInfo[C]
  
  def sequential(rules: GraphRewriteRules[C,D], maxProgCount: Int = 10): C => Set[C] = {e =>
    rules match {
      case r:SC => 
        r.out.close()
        r.out = new java.io.FileWriter("allgraph.dot")
      case _ =>
    }
    println(e)
    val gen = GraphGenerator(rules, e)
    val graphs = gen.take(maxProgCount).toList.map(Transformations.transpose(_))//.distinct
    println("done")
    graphs.map(HigherResiduator("_p" + _.toString()).residuate).map(normalize).toSet
  }
  
  def supertree(rules: GraphRewriteRules[C,D], outp: Boolean = false): C => Set[C] = {e =>
    rules match {
      case r:SC => 
        r.out.close()
        r.out = new java.io.FileWriter("allgraph.dot")
      case _ =>
    }
    println(e)
    val sgg = SuperGraphGenerator(rules, e)
    if(outp) {
      val g = new java.io.FileWriter("super.dot")
      g.write(SuperGraphGenerator.tgraph2dot(sgg.tgraph))
      g.close()
    }
    val tgraphs = SuperGraphGenerator.super2list(sgg.tgraph).distinct
    tgraphs.map(HigherResiduator("_p" + _.toString()).residuate).map(normalize).toSet
  }
  
  def caching(sc: C => Set[C]): C => Set[C] = mutableHashMapMemo.apply(sc)
  
}

object Test  {
  
  import HSupecompilers._

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
    addp("nrev", "Y \\ f x -> case x of { S x -> add (f x) (S(Z)); Z -> Z; }")
    
	//val add = p("\\a b -> (Y \\ f x y -> case x of { S x -> S (f x y); Z -> y; }) b a")
	//val add = p("Y \\ f x -> case x of { S x -> S (f x); Z -> Z; }")
    
    val expr = HigherGlobals.getByName("nrev")
    
	def test(h: HExpr[String]) {
      val d = HCall(h, List(p("S (S (S (Z)))")/*, p("S (S (S (Z)))")*/))
      //val d = HCall(h, List(p("S (Z)")))
      println(evaluate(d))
      //printCounters()
      //println("")
    }
	
    println(expr)
	test(expr)
	
	val mainsc = caching(supertree(SC()))
	//val mainsc = caching(sequential(SC(), 100))
	val twosc = supertree(SCTwo(mainsc), true)
	//val twosc = sequential(SCTwo(mainsc), 100)
	
	val sc = twosc(expr)
	//val sc = mainsc(expr)
	println(sc.size)
    val minp = sc.min(Ordering.by((s:HExpr[String]) => hsize(s)))
    println("\n" + minp + "\n")
    val dminp = sc.min(Ordering.by((s:HExpr[String]) => hdepth(s)))
    println("\n" + dminp + "\n")
	for(s1 <- sc) {
	  test(s1)
	}
  }

}