package mrsc.frontend

import mrsc._
import mrsc.core._
import mrsc.pfp._
import NamelessShows._

import org.rogach.scallop._
import com.twitter.util.Eval
import ec.Evolve

object CLI {
  
  class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    version("MRSC command-line interface, version 0.1")
    banner("Usage: mrsc-cli [OPTIONS] file")

    val test = opt[Boolean](descr = "Check residual programs by running user-specified tests")
    
    val prove = opt[Boolean](descr = 
      "Prove the propositions specified in the input file")
    
    val evolve = new Subcommand("evolve") {
      val trargs = trailArg[List[String]](required = true)
    }
      
    val resid = opt[Boolean](descr = "Residualize the function specified in the input file")
    
    val sc = opt[String](default = Some("custom"), descr = "Preset supercompiler")
    val driving = opt[String](default = Some("positive"), descr = "Driving method")
    val ec = opt[String](default = Some("all"), descr = "Embedding candidates")
    val whistle = opt[String](default = Some("HE3ByCouplingWhistle"), descr = "Whistle")
    val rebuild = opt[String](default = Some("UpperMsgOrLowerMsgOnBinaryWhistle"), 
        descr = "Rebuildings")
    val gen = opt[List[Int]](descr = "Genome")
    
    val timeout = opt[Int](default = Some(0), descr = "Timeout")
        
    val verbose = opt[Boolean](descr = "Be more verbose")
    
    val file = trailArg[List[String]](required = true)
  }
  
  def selStr[T](pairs: (String, T)*)(str1: String): T = {
    val str = str1.toLowerCase()
    val dt =
      for((s1,t) <- pairs) yield {
        val s = s1.toLowerCase()
        if(s == str) return t
        (str == s.take(str.size), s1, t)
      }
    val maxs = dt.filter(_._1 == dt.maxBy(_._1)._1)
    if(maxs.map(_._3).distinct.length != 1) {
      System.err.println(
          "Cannot find a match for '" + str + "', candidates:\n" + maxs.map(_._2).mkString("\n"))
      exit(2)
    }
    maxs(0)._3
  }
  
  def mkSupercompiler(conf: Conf): PFPSC = {
    conf.sc() match {
      case "deforest" => Deforester
      case "int" => InteractiveMRSC
      case "sc1" => SC1
      case "sc2" => SC2
      case "sc3" => SC3
      case "my" =>
        import Combinators._
        val w = withHistFilterW(control, he3ByCouplingWhistle)
        val reb = orElse(upperBiRebuilding(msg), lowerBiRebuilding(msg))
        val reb1 = concat(upperBiRebuilding(mkBiRebuilder(appRebuilder)), lowerBiRebuilding(mkBiRebuilder(appRebuilder)))
        val reb2 = rebuildingSCRule(allRebuildings)
        val appreb = rebuildingSCRule(appRebuilder)
        mkSC(orElse(folding, withWhistleOrElse(w, reb, driving)))
        mkSC(concat(folding, ifNoWhistle(sizeWhistle(20), concat(reb2, driving))))
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
            """)
    }
  }
  
  def main(args: Array[String]) {
    //val args = "--sc my -- /home/mouseentity/projs/graphsc/samples/add-assoc".split(" ")
    if(args.size >= 1 && args(0) == "evolve") {
      Evolve.main(args.tail)
    }
    else {
      val conf = new Conf(args)
      val problem = new EqProvingProblem
      problem.timeout = conf.timeout()
      problem.addFiles(conf.file())
      val sc =
        if(conf.gen.isSupplied) {
          val p = SCBuilder.SCParamDescr.ints2param(conf.gen())
          System.err.println(p)
          SCBuilder.mkSC(p)
        }
        else 
          mkSupercompiler(conf)
      val fit = problem.evaluateSC(sc, "sc")
      val goodfits = fit.filter(_ < 100)
      System.err.println("Evaluated: " + 
          goodfits.size + " " + goodfits.sum + " " + fit)
    }
  }
}

class LoggingGG(rules1: GraphRewriteRules[MetaTerm, Label], conf1: MetaTerm, withHistory1: Boolean = false)
  extends GraphGenerator[MetaTerm, Label](rules1, conf1, withHistory1) {

  import scala.collection.mutable.Queue
  import scala.collection.mutable.ListBuffer
  
  protected override def normalize(): Unit =
    while (completeGs.isEmpty && !pendingGs.isEmpty) {
      val pendingDelta = ListBuffer[SGraph[MetaTerm, Label]]()
      val g = pendingGs.head
      val steps = rules.steps(g)
      g.current.conf match {
        case t:Term =>
          println("\nterm:\n" + NamedSyntax.named(t))
        case c =>
          println("\nterm(?):\n" + c)
      }
      for(s <- steps)
        println(s)
      println("")
      val rewrittenGs = steps map { GraphGenerator.executeStep(_, g, withHistory) }
      for (g1 <- rewrittenGs)
        if (g1.isComplete) {
          completeGs.enqueue(g1)
          println("!!! New complete graph!")
        } else {
          pendingDelta += g1
        }
      pendingGs = pendingDelta ++: pendingGs.tail
    }
}
