package mrsc.frontend

import mrsc.core._
import mrsc.pfp._
import NamelessSyntax._

object Combinators {
  type C = MetaTerm
  type D = Label
  type N = SNode[C, D]
  type S = GraphRewriteStep[C, D]
  
  type History = (GContext, List[N])
  
  type Rule[T] = T => List[S]
  type SCRule = Rule[History]
  
  def mkSC(r: SCRule): PFPSC = { gc =>
    new PFPRules with MyVarGen {
      override def steps(g: G): List[S] = {
        r(gc, g.current :: g.current.ancestors)
      }
      
      def inspect(g: G): Signal = None
      def fold(signal: Signal, g: G): List[S] = Nil
      def drive(signal: Signal, g: G): List[S] = Nil
      def rebuild(signal: Signal, g: G): List[S] = Nil
    }
  }
  
  def orElse(a: SCRule, b: SCRule): SCRule =
    h => a(h) match {
      case Nil => b(h)
      case ss => ss
    }
    
  def andAlso(a: SCRule, b: SCRule): SCRule =
    h => a(h) match {
      case Nil => Nil
      case ss => ss ++ b(h)
    }
  
  def concat(a: SCRule, b: SCRule): SCRule =
    h => a(h) ++ b(h)
  
  def alternateLists[T](a: List[T], b: List[T]): List[T] = (a,b) match {
      case (Nil, _) => b
      case (_, Nil) => a
      case (ha :: ta, hb :: tb) => ha :: hb :: alternateLists(ta, tb)
    }
    
  def alternate(a: SCRule, b: SCRule): SCRule =
    h => alternateLists(a(h), b(h))
  
  type HistFilter = History => History
  type Whistle = History => History
  
  def withWhistle(w: Whistle, r: SCRule): SCRule =
    h => w(h) match {
      case (_,Nil) => Nil
      case h1 => r(h1)
    }
    
  def withWhistleOrElse(w: Whistle, r: SCRule, e: SCRule): SCRule =
    h => w(h) match {
      case (_,Nil) => e(h)
      case h1 => r(h1)
    }
    
  def ifNoWhistle(w: Whistle, r: SCRule): SCRule =
    h => w(h) match {
      case (_,Nil) => r(h)
      case h1 => Nil
    }
  
  def ifWhistle(w: Whistle, r: SCRule): SCRule =
    h => w(h) match {
      case (_,Nil) => r(h)
      case h1 => Nil
    }
    
  def orW(w1: Whistle, w2: Whistle): Whistle =
    h => w1(h) match {
      case (_,Nil) => w2(h)
      case h1 => h1
    }
  
  def andW(w1: Whistle, w2: Whistle): Whistle =
    h => w1(h) match {
      case h1@(_,Nil) => h1
      case h1 => w2(h)
    }
    
  def compW(w1: Whistle, w2: Whistle): Whistle =
    h => w1(h) match {
      case h1@(_,Nil) => h1
      case h1 => w2(h1)
    }
    
  def thenAlways(w: Whistle): Whistle = {
    def fun(h: History): History = h._2 match {
      case Nil => (h._1, Nil)
      case _ => w(h) match {
        case (_,Nil) => fun((h._1, h._2.tail))
        case h1 => h1
      }
    }
    fun
  }
    
  def maxW(w1: Whistle, w2: Whistle): Whistle =
    orW(andW(thenAlways(w1), w2), andW(thenAlways(w2), w1))
    
  def depthWhistle(d: Int): Whistle =
    h => if(h._2.size >= d) (h._1, List(h._2.head)) else (h._1, Nil)
    
  def sizeWhistle(s: Int): Whistle =
    h => h._2.head.conf match {
      case t:Term if t.size >= s => (h._1, List(h._2.head))
      case _ => (h._1, Nil)
    }
  
  
  def withHistFilter(f: HistFilter, r: SCRule): SCRule =
    h => r(f(h))
    
  def withHistFilterW(f: HistFilter, w: Whistle): Whistle =
    h => w(f(h))
    
    
  var myFreeVar = 100
  def myNextVar(x: Any = ()): FVar = {
    myFreeVar += 1
    FVar(myFreeVar)
  }
  trait MyVarGen extends VarGen {
    override def nextVar(x: Any = ()) = myNextVar(x)
  }
    
  case class usefulFuns(h: History) extends PFPSemantics with MyVarGen {
    override val gc = h._1 
  }
    
    
  def driving: SCRule = 
    h => List(usefulFuns(h).driveStep(h._2.head.conf).graphStep)

  def drivingLet: SCRule =
    h => {
      val mstep = usefulFuns(h).driveStep(h._2.head.conf) match {
        case DecomposeRebuildingMStep(rb) =>
          FreezeRebuildingMStep(rb)
        case ms => ms
      }
      List(mstep.graphStep)
    }
    
  def drivingPositive: SCRule =
    h => {
      val ds = usefulFuns(h).driveStep(h._2.head.conf) match {
        case VariantsMStep(sel, bs) =>
          val bs1 = bs map { case (ptr, ctr, next) => (ptr, ctr, applySubst(next, Map(sel -> ctr))) }
          VariantsMStep(sel, bs1)
        case s =>
          s
      }
      List(ds.graphStep)
    }
    
  def folding: SCRule =
    h => h._2.tail find { n => subclass.equiv(h._2.head.conf, n.conf) } map 
          { n => FoldStep(n.sPath): S } toList
 
  def justStop: SCRule =
    h => if(h._2.head.conf.isInstanceOf[Term]) List(CompleteCurrentNodeStep()) else Nil
          
  def control: HistFilter =
    h => {
        def isGlobal(n: N): Boolean = n.conf match {
          case t: Rebuilding => false
          case t: Term =>
            Decomposition.decompose(t) match {
              case Context(RedexCaseAlt(_, _)) => true
              case _                           => false
            }
        }
      
        def trivial(n: N): Boolean = n.conf match {
          case t: Rebuilding => true
          case t: Term =>
            Decomposition.decompose(t) match {
              case Context(RedexLamApp(lam, app)) => true
              case Context(_)                     => false
              // observable
              case _                              => true
            }
        }
      
      val n = h._2.head 
      if(isGlobal(n)) {
        (h._1, n :: h._2.tail.filter(isGlobal(_)))
      } else {
        (h._1, n :: h._2.tail.takeWhile(!isGlobal(_)).filter(!trivial(_)))
      }
    }
    
  
    
  def orderingWhistle(ordering: PartialOrdering[MetaTerm]): Whistle =
    h => (h._1, 
          h._2.tail.find{ n => ordering.lteq(n.conf, h._2.head.conf) }
            .fold[List[N]](Nil)(n => h._2.head :: List(n)))
  
  def he3Whistle: Whistle =
    orderingWhistle(HE3Ordering)
  
  def he3ByCouplingWhistle: Whistle =
    orderingWhistle(HE3ByCouplingOrdering)
    
  
  type Rebuilder = N => List[Rebuilding]
  // First arg is the one that's being rebuilt
  type BiRebuilder = (N, N) => List[Rebuilding]
  
  def rebuildingSCRule(r: Rebuilder): SCRule =
    h => r(h._2.head).map(RebuildStep(_): S)
    
  def upperBiRebuilding(r: BiRebuilder): SCRule = {
    case (_,Nil) => Nil
    case (_,h::t) => 
      t.flatMap { n =>
        r(n, h).map { rb => RollbackStep(n.sPath, rb): S }
      }
  }
    
  def lowerBiRebuilding(r: BiRebuilder): SCRule = {
    case (_,Nil) => Nil
    case (_,h::t) => 
      t.flatMap { n =>
        r(h, n).map { rb => RebuildStep(rb): S }
      }
  }
  
  def mkBiRebuilder(r: Rebuilder): BiRebuilder =
    (n1,n2) => r(n1)
  
  
  def allRebuildings: Rebuilder =
    n => {
      val rg = new RebuildingsGenerator with MyVarGen {}
      rg.rebuildings(n.conf)
    }
    
  def appRebuilder: Rebuilder =
    n => {
      def rebuild(t: MetaTerm): List[Rebuilding] = t match {
        case App(fun, arg, _) =>
          rebuild(fun) match {
            case Nil =>
              val fv = myNextVar()
              List(Rebuilding(App(fun, fv), Map(fv -> arg)))
            case rs => rs.map { 
              case Rebuilding(ter, mp, _) =>
                val fv = myNextVar() 
                Rebuilding(App(ter, fv), mp + (fv -> arg))
            }
          }
        case _ => Nil
      }
      rebuild(n.conf).filter(r => !r.sub.values.forall(_.isInstanceOf[FVar]))
    }
    
  def mutualGens: BiRebuilder =
    (n1,n2) => {
      val rg = new MutualGens with MyVarGen {}
      rg.mutualGens(n1.conf, n2.conf) 
    }
    
  def msg: BiRebuilder =
    (n1,n2) => {
      val rg = new MSG with MyVarGen {}
      rg.strictTermMSG(n1.conf.asInstanceOf[Term], n2.conf.asInstanceOf[Term]).toList
    }
}
