package mrsc.frontend

import mrsc._
import mrsc.core._
import mrsc.pfp._
import NamelessShows._

import org.rogach.scallop._

object CLI {
  
  class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    version("MRSC command-line interface, version 0.1")
    banner("Usage: mrsc-cli [OPTIONS] file")

    val test = opt[Boolean](descr = "Check residual programs by running user-specified tests")
    
    val prove = opt[Boolean](descr = 
      "Prove the propositions specified in the input file")
    
    val resid = opt[Boolean](descr = "Residualize the function specified in the input file")
    
    val verbose = opt[Boolean](descr = "Be more verbose")
    
    val file = trailArg[String](required = true)
  }
  
  def mkSupercompiler(conf: Conf, gcont: GContext): PFPRules = {
    class ClassicSC(val gc: GContext) extends PFPRules
      with PFPSemantics
      with PositiveDriving
      with AllFoldingCandidates
      with Folding
      with AllEmbeddingCandidates
      with HE3ByCouplingWhistle
      with DoubleRebuildingsOnBinaryWhistle
      
    new ClassicSC(gcont)
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