package mrsc.frontend

import mrsc._
import mrsc.core._
import mrsc.pfp._
import NamelessShows._

import org.rogach.scallop._
import com.twitter.util.Eval


object CLI {
  
  class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    version("MRSC command-line interface, version 0.1")
    banner("Usage: mrsc-cli [OPTIONS] file")

    val test = opt[Boolean](descr = "Check residual programs by running user-specified tests")
    
    val prove = opt[Boolean](descr = 
      "Prove the propositions specified in the input file")
    
    val resid = opt[Boolean](descr = "Residualize the function specified in the input file")
    
    val sc = opt[String](default = Some("custom"), descr = "Preset supercompiler")
    val driving = opt[String](default = Some("positive"), descr = "Driving method")
    val ec = opt[String](default = Some("all"), descr = "Embedding candidates")
    val whistle = opt[String](default = Some("HE3ByCouplingWhistle"), descr = "Whistle")
    val rebuild = opt[String](default = Some("UpperMsgOrLowerMsgOnBinaryWhistle"), 
        descr = "Rebuildings")
    
    val verbose = opt[Boolean](descr = "Be more verbose")
    
    val file = trailArg[String](required = true)
  }
  
  def selStr[T](pairs: (String, T)*)(str1: String): T = {
    val str = str1.toLowerCase()
    val dt =
      for((s1,t) <- pairs) yield {
        val s = s1.toLowerCase()
        if(s == str) return t
        ((s zip str).takeWhile{ case (a,b) => a == b }.length, s1, t)
      }
    val maxs = dt.filter(_._1 == dt.maxBy(_._1)._1)
    if(maxs.map(_._3).distinct.length != 1) {
      System.err.println(
          "Cannot find a match for '" + str + "', candidates:\n" + maxs.map(_._2).mkString("\n"))
      exit(2)
    }
    maxs(0)._3
  }
  
  def mkSupercompiler(conf: Conf, gcont: GContext): PFPRules = {
    conf.sc() match {
      case "deforest" => new Deforester(gcont)
      case "int" => new InteractiveMRSC(gcont)
      case "sc1" => new SC1(gcont)
      case "sc2" => new SC2(gcont)
      case "sc3" => new SC3(gcont)
      case "custom" =>
        implicit def strToPair(s: String): (String, String) = (s, s)
        
        val driving = 
          selStr(
              "PositiveDriving", 
              "NonpositiveDriving" -> "Driving",
              "LetDriving"
              )(conf.driving())
        
        val ec = 
          selStr(
              "AllEmbeddingCandidates",
              "ControlEmbeddingCandidates"
              )(conf.ec())
        
        val whistle = 
          selStr(
              "NoWhistle",
              "none" -> "NoWhistle",
              "HE3Whistle",
              "HE3ByCouplingWhistle"
              )(conf.whistle())
        
        val rebuild = 
          selStr(
              "NoRebuildings",
              "none" -> "NoRebuildings",
              "AllRebuildings",
              "LowerRebuildingsOnBinaryWhistle",
              "LowerAllBinaryGensOnBinaryWhistle",
              "UpperRebuildingsOnBinaryWhistle",
              "DoubleRebuildingsOnBinaryWhistle",
              "UpperAllBinaryGensOnBinaryWhistle",
              "DoubleAllBinaryGensOnBinaryWhistle",
              "LowerAllBinaryGensOrDriveOnBinaryWhistle",
              "UpperAllBinaryGensOrDriveOnBinaryWhistle",
              "UpperMsgOnBinaryWhistle",
              "UpperMsgOrLowerMggOnBinaryWhistle",
              "LowerMsgOrUpperMggOnBinaryWhistle",
              "LowerMsgOrDrivingOnBinaryWhistle",
              "LowerMsgOrUpperMsgOnBinaryWhistle",
              "UpperMsgOrLowerMsgOnBinaryWhistle",
              "DoubleMsgOnBinaryWhistle"
              )(conf.rebuild())
              
        val mixins = List(driving, "AllFoldingCandidates", "Folding", ec, whistle, rebuild)
        
        Eval[PFPSC]("""
            import mrsc.pfp._  
            class SC(val gc: GContext) extends PFPRules
              with PFPSemantics with """ + mixins.mkString(" with ") + """
            ((g:GContext) => new SC(g))
            """)(gcont)
    }
  }
  
  type SG = SGraph[MetaTerm, Label]
  
  def findEqual(i1: Iterator[Term], i2: Iterator[Term], grsize: Int = 10): Option[Term] = {
    val set1 = collection.mutable.Set[Term]()
    val set2 = collection.mutable.Set[Term]()
    
    val j1 = i1.grouped(grsize)
    val j2 = i2.grouped(grsize)
    
    def go(j: Iterator[Seq[Term]], 
           myset: collection.mutable.Set[Term], 
           oset: collection.mutable.Set[Term]): Option[Term] = {
      if(j.hasNext) {
        val n = j.next
        for(t <- n) {
          if(oset.contains(t)) return Some(t)
        }
        myset ++= n
      }
      None
    }
    
    while(j1.hasNext || j2.hasNext) {
      go(j1, set1, set2) match { case None => ; case Some(x) => return Some(x) }
      go(j2, set2, set1) match { case None => ; case Some(x) => return Some(x) }
    }
    
    println("set1: " + set1.size)
    println("set2: " + set2.size)
    
    None
  }
  
  
  def residualize(s: SG): Term = 
    Residuator(Transformations.transpose(s)).result
  
  def peelAbs(t: Term, v: Int = 0): Term = t match {
    case Abs(t1, _) => peelAbs(NamelessSyntax.termSubstTop(FVar(v), t1), v + 1)
    case _ => t
  }
  
  def main(args: Array[String]) {
    val conf = new Conf(args)
    val prog = 
      ProgramParser.parseFile(conf.file())
        .resolveUnbound.mergeAppsAndLambdas.topLevelEtaExpand.splitTests
    val gcont = prog.toGContext
    
    
    val tests =
      for(t <- prog.tests; if(conf.test())) yield {
        if(conf.verbose())
          System.err.println("Running test: " + t)
        val res = CBNEval.eval(t.toTerm(), gcont)
        if(conf.verbose())
          System.err.println("Result: " + res)
        t match {
          case ExprCall(e, es) => 
            (peelAbs(e.toTerm()), es.map(_.toTerm()), res)
          case _ => (t.toTerm(), Nil, res)
        }
      }
    
    def runTests(t_unpeeled: Term): Term => Term = {
      if(conf.test()){
        val big_number = 1000
        val t_peeled = peelAbs(t_unpeeled, big_number)
        val ts =
          for((t, as, res) <- tests; sub <- NamelessSyntax.findSubst(t_peeled, t)) yield
            (sub, as, res)
        if(ts.isEmpty) {
            System.err.println("No tests found for " + t_peeled)
            (x => x)
        } else {
          x =>
            for((sub,as,res) <- ts) {
              val fullsub = 
                sub.mapValues {
                  case FVar(v, _) => as(v)
                  case o => o
                }
              val term = NamelessSyntax.applySubst(peelAbs(x, big_number), fullsub)
              assert(res == CBNEval.eval(term, gcont))
            }
            x
        }
      }
      else
        (x => x)
    }
    
    val sc = mkSupercompiler(conf, gcont)
    
    if(conf.prove())
      for(p <- prog.prove) p match {
        case PropEq(e1, e2) =>
          val t1 = e1.bindUnbound.toTerm()
          val t2 = e2.bindUnbound.toTerm()
          
          findEqual(
              GraphGenerator(sc, t1).map(residualize).map(runTests(t1)), 
              GraphGenerator(sc, t2).map(residualize).map(runTests(t2))) match {
            case None => 
              System.err.println("Cannot prove the proposition: " + p)
            case Some(t) =>
              System.err.println("Proposition successfully proved: " + p)
              System.err.println(t)
          }
        case _ =>
          System.err.println("Proposition type is not supported: " + p)
      }
  }
}