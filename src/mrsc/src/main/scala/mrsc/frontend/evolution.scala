package mrsc.frontend

import mrsc.core._
import mrsc.pfp._
import com.twitter.util.Eval
import java.io.File
import ec._
import ec.simple._
import ec.util._
import ec.vector._
import ec.multiobjective.MultiObjectiveFitness
import java.util.concurrent.TimeoutException

sealed trait Param {
  def size: Int = this match {
    case ParamString(_) => 1
    case ParamInt(_) => 1
    case ParamRecord(fs) => fs.map(_._2.size).sum 
  }
  
  def apply(s: String): Param = 
    this.asInstanceOf[ParamRecord].fields.find(_._1 == s).get._2
    
  override def toString = this match {
    case ParamString(s) => s
    case ParamInt(i) => i.toString
    case ParamRecord(fs) => 
      fs.toList.map{ case (s,v) => s + " -> " + v.toString.replaceAll("\n", "\n  ") }
        .mkString("{\n", "\n", "\n}")
  }
}

case class ParamString(str: String) extends Param { override def toString = str }
case class ParamInt(int: Int) extends Param
case class ParamRecord(fields: List[(String, Param)]) extends Param

sealed trait ParamDescription {
  def param2ints(p: Param): List[Int] = this match {
    case ParamDescrOneOf(strs) =>
      List(strs.indexOf(p.asInstanceOf[ParamString].str))
    case ParamDescrInt(_, _) =>
      List(p.asInstanceOf[ParamInt].int)
    case ParamDescrRecord(fs) =>
      val ParamRecord(fields) = p
      fs.toList.flatMap(p => p._2.param2ints(fields.find(_._1 == p._1).get._2))
  }
  
  def ints2param(l: List[Int]): Param = this match {
    case ParamDescrOneOf(strs) =>
      ParamString(strs(l(0)))
    case ParamDescrInt(_, _) =>
      ParamInt(l(0))
    case ParamDescrRecord(fs) =>
      var curl = l
      val pars =
        for((s, pd) <- fs.toList) yield {
          val par = pd.ints2param(curl)
          curl = curl.drop(par.size)
          (s, par)
        }
      ParamRecord(pars)
  }
  
  def size: Int = this match {
    case ParamDescrOneOf(_) => 1
    case ParamDescrInt(_, _) => 1
    case ParamDescrRecord(fs) => fs.map(_._2.size).sum 
  }
  
  def bounds: List[(Int, Int)] = this match {
    case ParamDescrOneOf(ss) => List((0, ss.size - 1))
    case ParamDescrInt(mn, mx) => List((mn, mx))
    case ParamDescrRecord(fs) => fs.flatMap(_._2.bounds).toList
  }
}

case class ParamDescrOneOf(strs: List[String]) extends ParamDescription
case class ParamDescrInt(min: Int, max: Int) extends ParamDescription
case class ParamDescrRecord(fields: List[(String, ParamDescription)]) extends ParamDescription

object SCBuilder {
  def oneOf(ss: String*) = ParamDescrOneOf(ss.toList)
  
  val SCParamDescr = ParamDescrRecord(List(
      "driving" -> oneOf(
        "PositiveDriving", 
        "Driving",
        "LetDriving"),
      "ec" -> oneOf(
        "AllEmbeddingCandidates",
        "ControlEmbeddingCandidates"),
      "whistle" -> oneOf(
        "NoWhistle",
        "HE3Whistle",
        "HE3ByCouplingWhistle"),
      "rebuild" -> oneOf(
        "NoRebuildings",
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
        "DoubleMsgOnBinaryWhistle"),
      "maxdepth" -> ParamDescrInt(1,500)
      ))
      
  def scCode(p: Param): String = {
    val mixins = 
      List(p("driving"), "AllFoldingCandidates", "Folding", p("ec"), p("whistle"), p("rebuild"),
          "DepthGraphFilter")
    """import mrsc.pfp._  
    class SC(val gc: GContext) extends PFPRules with PFPSemantics with """ + 
    mixins.mkString(" with ") + " { override val maxDepth = " + p("maxdepth") + " }" + 
    "\n((g:GContext) => new SC(g))"
  }
      
  def mkSC(p: Param): PFPSC = {
    (new Eval)[PFPSC](scCode(p))
  }
}

trait SupercompilationProblem extends Problem with SimpleProblemForm {
  
  def evaluateSC(sc: PFPSC, info: String): List[Float]
  
  def vec2par(state: EvolutionState, vec: IntegerVectorIndividual): Param = {
    try {
      SCBuilder.SCParamDescr.ints2param(vec.genome.toList)
    } catch {
      case e:Throwable =>
        val bnds = SCBuilder.SCParamDescr.bounds
        val con =
          vec.genome.toList + "\n" +
          "pop.subpop.0.species.genome-size = " + bnds.size + "\n" +
            (for(((mn,mx), i) <- bnds.zipWithIndex) yield {
              "pop.subpop.0.species.min-gene." + i + " = " + mn + "\n" +
              "pop.subpop.0.species.max-gene." + i + " = " + mx + "\n"
            }).reduce(_ + _)
        state.output.warning(e.toString())
        state.output.fatal("The int vector doesn't satisfy the constraints:\n" + con)
        throw e
    }
  }
  
  override def describe(state: EvolutionState, ind: Individual, sp: Int, th: Int, log: Int) {
    ind match {
      case vec: IntegerVectorIndividual =>
        val par = vec2par(state, vec)
        state.output.log(log).writer.println(
            "Description of " + vec.genome.toList.mkString(" ") + ":\n" + par)
      case _ =>
        state.output.fatal("Individual must be an int vector")
    }
  }
  
  override def evaluate(state: EvolutionState, ind: Individual, sp: Int, th: Int) {
    if(ind.evaluated) return
    ind match {
      case vec: IntegerVectorIndividual =>
        val fitness = vec.fitness.asInstanceOf[MultiObjectiveFitness]
        
        val par = vec2par(state, vec)
          
        val info = vec.genome.toList.mkString(" ") + "\n" + par
        state.output.message("Evaluating " + info)
        
        val sc = 
          try {
            state.output.message("Compiling...")
            SCBuilder.mkSC(par)
          } catch {
            case e:Throwable =>
              state.output.warning("Error while building a supercompiler:\n" + 
                  "thread: " + th + "\n" + e + "\n" + info + 
                  "\n\n" + SCBuilder.scCode(par) + "\n")
              null
          }
          
        val fit =
          try {
            state.output.message("Evaluating...")
            evaluateSC(sc, info)
          } catch {
            case e:Throwable =>
              state.output.warning("Error while evaluating a supercompiler:\n" + 
                  "\n" + e + "\n" + vec.genome.mkString(" ") + "\n" + par + "\n")
              null
          }
        
        val goodfits = fit.filter(_ < 100)
          
        state.output.message("Evaluated " + vec.genome.mkString(" ") + ": " + 
            goodfits.size + " " + goodfits.sum + " " + fit)
          
        vec.fitness match {
          case fitness: MultiObjectiveFitness =>
            // minimize the number of residuations spent on each problem
            if(fit == null) fitness.setObjectives(state, fitness.maxObjective)
            else fitness.setObjectives(state, fit.toArray)
          case fitness: SimpleFitness =>
            // maximize the number of solved problems
            fitness.setFitness(state, goodfits.size.toFloat - goodfits.sum/goodfits.size/100)
        }
        
        ind.evaluated = true
      case _ =>
        state.output.fatal("Individual must be an int vector")
    }
  }
  
}

class TestFailedException(s: String) 
  extends Exception("Test failed on a supercompiled program: " + s)

class EqProvingProblem extends SupercompilationProblem {

  var maxfit: Float = 99999.0f
  var timeout = 10
  var testing = true
  var progs: List[(String, Program, GContext, List[(Term, List[Term], Term)])] = Nil
  
  def addFiles(files: List[String]) {
    progs = progs ++
      (for(file <- files) yield {
        val prog = 
            ProgramParser.parseFile(file)
              .resolveUnbound.mergeAppsAndLambdas.topLevelEtaExpand.splitTests
        val gcont = prog.toGContext
        (file, prog, gcont, makeTests(prog, gcont))
      })
  }
  
  def makeTests(prog: Program, gcont: GContext): List[(Term, List[Term], Term)] = {
    for(t <- prog.tests; if testing) yield {
      val res = CBNEval.eval(t.toTerm(), gcont)
      t match {
        case ExprCall(e, es) => 
          (peelAbs(e.toTerm())._1, es.map(_.toTerm()), res)
        case _ => (t.toTerm(), Nil, res)
      }
    }
  }
  
  def addFileSet(file: String) {
    val src = scala.io.Source.fromFile(file)
    val parent = (new File(file)).getParent()
    val files =
      (for(l <- src.getLines; fn = l.trim(); if fn != "")
        yield parent + "/" + fn).toList
    src.close()
    addFiles(files)
  }
  
  override def setup(state: EvolutionState, base: Parameter) {
    testing = state.parameters.getBoolean(base.push("testing"), null, true)
    timeout = state.parameters.getIntWithDefault(base.push("timeout"), null, 10)
    val fileset = state.parameters.getString(base.push("fileset"), null)
    if(fileset == null)
      state.output.fatal("EqProverProblem: fileset must be specified")
    else
      addFileSet(fileset)
  }

  override def evaluateSC(sc: PFPSC, info: String): List[Float] = {
    (for((file, prog, gcont, tests) <- progs) yield {
      
      def runTests(t_unpeeled: Term): Term => Term = {
        if(testing) {
          val (t_peeled, peeled_abs) = peelAbs(t_unpeeled)
          val ts =
            for((t, as, res) <- tests; sub <- NamelessSyntax.findSubst(t_peeled, t)) yield {
//              println("tested: " + NamedSyntax.named(t))
//              println("args: " + as.map(NamedSyntax.named(_)))
//              println("t_peeled: " + NamedSyntax.named(t_peeled))
//              println("sub: " + sub)
              (sub, as, res)
            }
          if(ts.isEmpty) {
              //System.err.println("No tests found for " + t_peeled)
              (x => x)
          } else {
            x =>
              for((sub,as,res) <- ts) {
//                println("args: " + as.map(NamedSyntax.named(_)))
//                println("t_peeled: " + NamedSyntax.named(t_peeled))
//                println("x: " + NamedSyntax.named(x))
//                println("sub: " + sub)
                val varsub = as.zipWithIndex.map { case (a,i) => FVar(i) -> a }.toMap
                val fullsub = 
                  sub.mapValues (v => NamelessSyntax.applySubst(v, varsub))
//                println("fullsub: " + fullsub)
                val term =
                  (x /: (0 until peeled_abs))(
                      (a,i) => App(a, fullsub.getOrElse(FVar(i), as(i))))
//                println("term: " + NamedSyntax.named(term))
                val newres = CBNEval.eval(term, gcont)
                if(res != newres)
                  throw new TestFailedException("\n" + 
                      NamedSyntax.named(term) + "\n" + 
                      "should be: " + NamedSyntax.named(res) + "\n" +
                      "evalated:  " + NamedSyntax.named(newres))
              }
              x
          }
        }
        else
          (x => x)
      }
      
      for(p <- prog.prove) yield {
        try {
          System.err.println("running " + file + " : " + p)
          p match {
            case PropEq(e1, e2) if false =>
              val t1 = e1.bindUnbound.toTerm()
              val t2 = e2.bindUnbound.toTerm()
              
              
              //val gg1 = new LoggingGG(sc(gcont), t1).map(residualize).map(runTests(t1))
              //val gg2 = new LoggingGG(sc(gcont), t2).map(residualize).map(runTests(t2))
              
              val gg1 = GraphGenerator(sc(gcont), t1).map(residualize).map(runTests(t1))
              val gg2 = GraphGenerator(sc(gcont), t2).map(residualize).map(runTests(t2))
              
              withTimeout(findEqual(gg1, gg2), timeout) match {
                case None => 1111f // better than exit on timeout
                case Some(t) => t._2
              }
            case PropEq(e1, e2) =>
              val t1 = e1.bindUnbound.toTerm()
              val t2 = e2.bindUnbound.toTerm()
              
              
              //val gg1 = new LoggingGG(sc(gcont), t1).map(residualize).map(runTests(t1))
              //val gg2 = new LoggingGG(sc(gcont), t2).map(residualize).map(runTests(t2))
              
              //val gg1 = GraphGenerator(sc(gcont), t1).map(residualize).map(runTests(t1))
              //val gg2 = GraphGenerator(sc(gcont), t2).map(residualize).map(runTests(t2))
              
              val tr1 = runTests(t1)
              val tr2 = runTests(t2)
              
              val gg = (new EqProvingGG(sc(gcont), t1, sc(gcont), t2)).map {
                case (g1, g2) =>
                  val r1 = tr1(residualize(g1))
                  val r2 = tr2(residualize(g2))
                  
                  //println("left:\n" + NamedSyntax.named(r1))
                  //println("right:\n" + NamedSyntax.named(r2))
                  
                  r1 == r2
              }
              
              withTimeout(gg.zipWithIndex.find(_._1 == true), timeout) match {
                case None => 1111f // better than exit on timeout
                case Some(t) => t._2 + 1
              }
            case PropReturnsConstr(e1, ctr) =>
              val t1 = e1.bindUnbound.toTerm()
              val gg1 = GraphGenerator(sc(gcont), t1).map(residualize).map(runTests(t1))
              
              withTimeout(findReturning(gg1, ctr), timeout) match {
                case None => 1111f // better than exit on timeout
                case Some(t) => t._2
              }
            case _ =>
              System.err.println("Proposition type is not supported: " + p)
              1000f
          }
        } catch {
          case e:TimeoutException =>
            System.err.println("Timeout")
            2222f
          case e:Throwable =>
            System.err.println(e)
            System.err.println(info)
            System.err.println("While proving " + p + " from " + file)
            0 // This is a bug and we like bugs!
        }
      }
    }).flatten
  }
}

