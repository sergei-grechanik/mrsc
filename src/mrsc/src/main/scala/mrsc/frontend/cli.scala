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
      val sc = mkSupercompiler(conf)
      runSC(conf)(sc) 
    }
  }
  
  def runSC(conf: Conf): PFPSC => List[Int] = {
    val funs: List[PFPSC => List[Int]] =
      for(file <- conf.file()) yield {
        val prog = 
          ProgramParser.parseFile(file)
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
        
        if(conf.prove()) { (sc:PFPSC) =>
          for(p <- prog.prove) yield p match {
            case PropEq(e1, e2) =>
              val t1 = e1.bindUnbound.toTerm()
              val t2 = e2.bindUnbound.toTerm()
              
              findEqual(
                  GraphGenerator(sc(gcont), t1).map(residualize).map(runTests(t1)), 
                  GraphGenerator(sc(gcont), t2).map(residualize).map(runTests(t2))) match {
                case None => 
                  if(conf.verbose())
                    System.err.println("Cannot prove the proposition: " + p)
                  0
                case Some(t) =>
                  if(conf.verbose())
                    System.err.println("Proposition successfully proved: " + p)
                  1
              }
            case _ =>
              System.err.println("Proposition type is not supported: " + p)
              0
          }
        }
        else
          ((sc:PFPSC) => List(0))
      }
    
    (sc => funs.flatMap(f => f(sc)))
  }
}