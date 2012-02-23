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
  
//  type Warning = List[(N, HExpr[Either[(C,C), String]])]
//  def inspect(g: G): Option[Warning] = {
//    val gs = g.current.ancestors.map(n => (n, HigherSyntax.generalize(g.current.conf, n.conf)))
//    val gs1 = gs.filterNot(e => isVarAtom(e._2))
//    if(gs1.isEmpty)
//      None
//    else
//      Some(gs1)
//  }
  
  type Warning = List[N]
  def inspect(g: G): Option[Warning] =
    g.current.ancestors.filter(n => HHE.he(n.conf, g.current.conf) || !isVarAtom(generalize(g.current.conf, n.conf))) match {
      case Nil => None
      case l => Some(l)
  	}
  
  def rebuild(signal: Option[Warning], g: G): List[S] = signal match {
    case None => Nil
    case Some(l) =>
      (for(n <- l) yield {
        def sndPart(e: HExpr[Either[HExpr[String], String]]) =
          unbound(e).find(_.fold(_ => false, _.isLeft)).get match {
            case Right(Left(x)) => x 
          }
        
        val lgens = generalizations(g.current.conf) map sndPart filter containsFix
        val ugens =
          for(ge <- generalizations(n.conf) if containsFix(ge) && containsFix(sndPart(ge))) yield ge
        val uparts = ugens ++ ugens.map(sndPart)
        val alluppers = 
          for(ge <- generalizations(n.conf) if containsFix(ge) && containsFix(sndPart(ge))) yield {
        	  val l = renameUnbound(ge) map mapAtom(x => x.fold(y => y, HAtom(_)))
        	  UpperStep(n, DecomposeDriveStep(stdCompose[String], l).graphStep)
          }
        val alllowers =
          for(ge <- generalizations(g.current.conf)
        		  if uparts.exists(gg => 
        		    	HigherSyntax.equiv(ge, gg) || 
        		    	HigherSyntax.equiv(sndPart(ge), gg)) ||
        		  	 g.current.ancestors.exists(n =>
        		  	 	HigherSyntax.equiv(ge, n.conf) || 
        		  	 	HigherSyntax.equiv(sndPart(ge), n.conf))) yield {
        	  val l = renameUnbound(ge) map mapAtom(x => x.fold(y => y, HAtom(_)))
        	  DecomposeDriveStep(stdCompose[String], l).graphStep
          }
        
        val alllowers1 =
          for(ge <- generalizations(g.current.conf).sortBy(ge => -hsize(ge)*hsize(sndPart(ge))).take(1)) yield {
        	  val l = renameUnbound(ge) map mapAtom(x => x.fold(y => y, HAtom(_)))
        	  DecomposeDriveStep(stdCompose[String], l).graphStep
          }
        
        if(alllowers.isEmpty)
          alluppers ++ alllowers1
        else
          alluppers ++ alllowers
      }).flatten
  }
    
//  def rebuild(signal: Option[Warning], g: G): List[S] = signal match {
//    case None => Nil
//    case Some(l) =>
//      (for((n, e) <- l) yield {
//        
//        val l = renameUnbound(e)
//        val fun = l(0)
//        
//        val ls = l map mapAtom(x => x.fold(_._1, HAtom(_)))
//        val us = l map mapAtom(x => x.fold(_._2, HAtom(_)))
//        
//        val lstep = DecomposeDriveStep(stdCompose[String], ls)
//        val ustep = DecomposeDriveStep(stdCompose[String], us)
//        
//        def sndPart(e: HExpr[Either[HExpr[String], String]]) =
//          unbound(e).find(_.fold(_ => false, _.isLeft)).get match {
//            case Right(Left(x)) => x 
//          }
//        
//        val lgens = generalizations(g.current.conf) map sndPart filter nontrivialCall
//        val ugens = generalizations(n.conf) map sndPart filter nontrivialCall
//        val alluppers = 
//          for(ge <- generalizations(n.conf) if lgens.contains(sndPart(ge)) /*&& nontrivialCall(ge)*/) yield {
//        	  val l = renameUnbound(ge) map mapAtom(x => x.fold(y => y, HAtom(_)))
//        	  UpperStep(n, DecomposeDriveStep(stdCompose[String], l).graphStep)
//          }
//        val alllowers =
//          for(ge <- generalizations(g.current.conf) if HigherSyntax.equiv(ge, n.conf) /*&& nontrivialCall(g)*/) yield {
//        	  val l = renameUnbound(ge) map mapAtom(x => x.fold(y => y, HAtom(_)))
//        	  DecomposeDriveStep(stdCompose[String], l).graphStep
//          }
//        
//        
//        //println(alluppers.length)
//        if(!containsFix(fun))
//          alluppers ++ alllowers
//        else
//    	List(lstep.graphStep).filterNot(x => !HigherSyntax.equiv(fun, n.conf) || HigherSyntax.equiv(fun, g.current.conf)) ++
//    	alluppers ++ alllowers
//    	List(UpperStep(n, ustep.graphStep)).
//    		filterNot(x => HigherSyntax.equiv(fun, n.conf) || HigherSyntax.equiv(fun, g.current.conf))
//    		
//      }).flatten
//  }
  
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
      //val tooLate = hsize(g.current.conf) > Math.max(hsize((g.current :: g.current.ancestors).last.conf)*2, 10)
      //val tooLate = g.current.ancestors.length >= 10
      val tooLate = g.current.ancestors.exists(n => HHE.he(n.conf, g.current.conf)) || g.current.ancestors.length >= 10 
      val driveSteps = if(!tooLate) drive(g) else List()
      
      //println((g.completeNodes.size + g.incompleteLeaves.size) + " " + g.current.ancestors.length + " " + driveSteps.length)
      //print(hsize(g.current.conf) + " ")
      
//      out.write("// rebuild\n")
//      rebuildSteps map (drawStep(g.current, _, "[style=dashed]"))
//      out.write("// drive " + g.current.ancestors.length + "\n")
//      driveSteps map (drawStep(g.current, _, "[color=red]"))
//      out.flush()
      
      if(g.completeNodes.size > 3000) Nil else
      driveSteps ++ rebuildSteps
  }
}

case class SCTwo(baseSC: HExpr[String] => Set[HExpr[String]])
	extends SC with Memos {
  
  val mySC = mutableHashMapMemo.apply((x:HExpr[String]) =>
    baseSC(x).toList.sortBy(hsize(_)).take(100)
    )
  
  override def steps(g: G): List[S] = fold(g) match {
    case foldSteps if !foldSteps.isEmpty =>
      foldSteps
    case foldSteps =>
      val signal = inspect(g)
      val rebuildSteps = rebuild(signal, g).filter(_.isInstanceOf[UpperStep[C,DriveInfo[C]]])
      //val tooLate = hsize(g.current.conf) > Math.max(hsize((g.current :: g.current.ancestors).last.conf)*2, 10)
      val tooLate = g.current.ancestors.length >= 10 || g.current.ancestors.exists(a => HHE.he(a.conf, g.current.conf))
      val driveSteps = if(!tooLate) drive(g) else List()
      
//      val superSteps = 
//        if((g.current.in == null || !g.current.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]]) && 
//            g.current.ancestors.length < 15)
//          mySC(g.current.conf).
//          	filter(hsize(_) < hsize(g.current.conf)/*hsize((g.current :: g.current.ancestors).last.conf) + 5*/).
//          	filter(!HigherSyntax.equiv(_, g.current.conf)).
//          	take(1).map(TransientDriveStep(_).graphStep)
//        else
//          Nil
    
//      val sig1 =
//	      for(n <- g.current.ancestors; 
//			  x <- mySC(g.current.conf);
//			  y <- mySC(n.conf);
//			  ge = HigherSyntax.generalize(x,y);
//			  if !isVarAtom(ge) && !HigherSyntax.equiv(ge,y))
//	        yield (n,ge)
//      
//	  val superSteps = rebuild(Some(sig1.distinct), g).distinct.take(3)//.filter(_.isInstanceOf[UpperStep[C,DriveInfo[C]]])

//      val superSteps = 
//        if((g.current.in == null || !g.current.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]]) && 
//            !tooLate)
//          mySC(g.current.conf).
//          	filter(hsize(_) <= Math.max(hsize(g.current.conf), hsize((g.current :: g.current.ancestors).last.conf)) + 5).
//          	filter(!HigherSyntax.equiv(_, g.current.conf)).
//          	filter(l => g.current.in == null || g.current.ancestors.exists(r => !isVarAtom(HigherSyntax.generalize(l,r.conf)))).
//          	take(10).map(TransientDriveStep(_).graphStep)
//        else
//          Nil
        
      
      val curSced = mySC(g.current.conf)
      val presuperSteps =
        for(n <- g.current.ancestors if n.in == null || !n.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]];
    		p <- mySC(n.conf) if !HigherSyntax.equiv(p, n.conf); 
    		if curSced.exists(x => containsFix(generalize(x, p))))
          yield (n,p)
      
      val superSteps = 
        presuperSteps.sortBy(x => hsize(x._2)).take(2) map {case (n,p) => UpperStep(n, TransientDriveStep(p).graphStep)}
      
      println(superSteps.length)
      
      //if(g.current.in == null || !g.current.in.driveInfo.isInstanceOf[TransientStepInfo[HExpr[String]]])
      //  driveSteps ++ rebuildSteps ++ superSteps
      //else
      //  driveSteps ++ rebuildSteps ++ superSteps
      
      if(superSteps.isEmpty || tooLate)
        driveSteps ++ rebuildSteps
      else
        driveSteps ++ rebuildSteps ++ superSteps
      
//      if(!superSteps.isEmpty && hsize(superSteps(0).ns(0)._1) < hsize(g.current.conf))
//        superSteps
//      else
//        if(rebuildSteps.isEmpty)
//          driveSteps
//        else
//          rebuildSteps ++ superSteps
      
//      if(superSteps.isEmpty || hsize(superSteps(0).ns(0)._1) > hsize(g.current.conf))
//        driveSteps ++ rebuildSteps ++ superSteps
//      else
//        superSteps
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
  
  def imessy(m: Messy, e: HExpr[String]) = {
    var cur: MNode = m.conf2nodes(e)
    while(true) {
      println("\n\n========= CURRENT ==========")
      println(cur.conf)
      println("============================\n")
      var i = 0;
      val l = (for(e <- cur.outs; n <- e.dests) yield n).toList
      for(n <- l) {
        i += 1
        println("============= " + i + " ==============")
        println(n.conf)
      }
      val ch = readInt()
      cur = l(ch - 1)
    }
  }
  
  def messy(e: HExpr[String]): Set[HExpr[String]] = {
    val o = new java.io.FileWriter("allgraph.dot")
    val m = new Messy
    try {
      m.addConf(e)
    } catch {
      case _ => printf("limit reached =========")
    }
//    m.truncate()
//    m.residuate(e)
//    try {
//      m.levelUp()
//    } catch {
//      case _ => printf("limit reached =========")
//    }
    //imessy(m, e)
    m.truncate()
    //m.conf2nodes.values.toList.filter(x => containsFix(x.conf)).sortBy(-_.ins.size).take(10).map(x => println(x.conf))
    var resid = m.residuate2(false)
    val rs = resid(e)
    println("Residuals: " + rs.size)
    //val rsn = m.residuate2(true)(e)
    //println("Naive Residuals: " + rs.size)
    
    //if(rsn.toSet != rs.toSet)
    //  println("BUG!")
    
    for(i <- 1 to 1) {
      println(i)
      m.levelUp(resid)
      resid = m.residuate2()
      m.truncate()
      println("Residuals: " + resid(e).size)
    }
    
    o.write(m.toDot())
    o.close()
    
    resid(e).toSet.asInstanceOf[Set[HExpr[String]]]
    //throw new Exception
  }
  
  def main(args: Array[String]):Unit = {
    def p = HigherParsers.parseExpr _
    def addp(n: String, s: String) {
      val e = mapAtom(HigherGlobals.getByName)(p(s))
      HigherGlobals.add(n, e)
    }
    
    addp("add", "Y \\ f x y -> case x of { S x -> S (f x y); Z -> y; }")
    addp("mul", "Y \\ f x y -> case x of { S x -> add y (f x y); Z -> Z; }")
    addp("addAcc", "Y \\ f x y -> case x of { S x -> f x (S y); Z -> y; }")
    addp("add0", "Y \\ f x -> case x of { S x -> S (f x); Z -> Z; }")
    addp("add1", "Y \\ f x -> case x of { S x -> S (f x); Z -> S (Z); }")
    addp("add2", "Y \\ f x -> case x of { S x -> S (f x); Z -> S (S (Z)); }")
    addp("nrev", "Y \\ f x -> case x of { S x -> add (f x) (S(Z)); Z -> Z; }")
    addp("snrev", "Y \\ f x -> case x of { S x -> add1 (f x); Z -> Z; }")
    addp("rev", "\\ x -> addAcc x (Z)")
    addp("smth", "\\ x -> case (case x of {S v -> (S (add1 v));  Z  -> (S (Z ));}) of { S v -> (S (add1 v));  Z  -> (S (Z ));}")
    addp("or", "\\ x y -> case x of { T -> (T); F -> y; }")
    addp("even", "Y \\ f x -> case x of { S x -> case x of { S x -> f x; Z -> (F);}; Z -> (T); }")
    addp("evenBad", "Y \\ f x -> case x of { S x -> case (f x) of { T -> (F); F -> (T);}; Z -> (T); }")
    addp("odd", "Y \\ f x -> case x of { S x -> case (f x) of { T -> (F); F -> (T);}; Z -> (F); }")
    addp("orEvenOdd", "\\ x -> or (even x) (odd x)")
    addp("dbl", "Y \\ f x -> case x of { S x -> S (S (f x)); Z -> (Z);}")
    addp("dblAcc", "Y \\ f x y -> case x of { S x -> f x (S (S y)); Z -> (Z);}")
    addp("evenDbl", "\\ x -> even (dbl x)")
    addp("evenDblAcc", "\\ x -> even (dblAcc x (Z))")
    addp("trueOrBot", "Y \\ f x -> case x of { S x -> f x; Z -> (T); }")
    addp("a1a1nrev", "\\ x -> add1 (add1 (snrev x))")
    addp("idle", "Y \\ f x -> case x of { S x -> f(f x); Z -> (Z); }")
    addp("fict", "Y \\ f x y -> case x of { S x -> f x (S y); Z -> (Z); }")
    addp("lolo", "\\x y -> addAcc (snrev x) (S y)")
    
	//val add = p("\\a b -> (Y \\ f x y -> case x of { S x -> S (f x y); Z -> y; }) b a")
	//val add = p("Y \\ f x -> case x of { S x -> S (f x); Z -> Z; }")
    
    //val expr = mapAtom(HigherGlobals.getByName)(p("\\x y -> add (add x (S(Z))) y"))
    //val expr = HigherGlobals.getByName("fict")
    //val expr = HigherGlobals.getByName("idle")
    //val expr = HigherGlobals.getByName("add")
    //val expr = HigherGlobals.getByName("rev")
    val expr = HigherGlobals.getByName("snrev")
    //val expr = HigherGlobals.getByName("evenBad")
    //val expr = HigherGlobals.getByName("evenDblAcc")
    //val expr = HigherGlobals.getByName("a1a1nrev")
    
	def test(h: HExpr[String]): HExpr[String] = {
      val d = HCall(h, List(p("S (S (S (Z)))")/*, p("S (S (S (Z)))")*/))
      //val d = HCall(h, List(p("S (S (S (Z)))"), p("S (S (S (Z)))")))
      //val d = HCall(h, List(p("S (Z)")))
      evaluate(d)
      //printCounters()
      //println("")
    }
	
    def sizes(h: HExpr[String]): String =
      "size: " + hsize(h) + " depth: " + hdepth(h) + " smth: " + hsomething(h)
    
    println(expr)
	println(test(expr))
	
	val mainsc = caching(supertree(SC()))
	val mainsc1 = caching(supertree(SC(), true))
	//val mainsc = caching(sequential(SC(), 100))
	val twosc = supertree(SCTwo(mainsc), true)
	//val twosc = sequential(SCTwo(mainsc), 100)
	
	val sc = messy(expr)
	//val sc = twosc(expr)
	//val sc = mainsc1(expr)
	println(sc.size)
    //val minp = sc.min(Ordering.by((s:HExpr[String]) => hsize(s)))
    val sorted = sc.toList.sortBy(hsize(_))
    println("\nsmallest:")
    for(i <- sorted.take(3))
      println("\n" + sizes(i) + "\n" + i + "\n")
    val ssorted = sorted.take(100).sortBy(_.toString.size)
    println("\nchosen:")
    for(i <- ssorted.take(3))
      println("\n" + sizes(i) + "\n" + i + "\n")
    
    println("==============================")
    sorted.map(test).distinct.map(println)
    println("==============================\n")
    
    println("original: " + hsize(expr))
    println("min: " + hsize(sorted(0)) + " max: " + hsize(sorted.last) + " avg: " + sorted.map(hsize).sum/sorted.size)
  }

}