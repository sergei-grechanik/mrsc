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