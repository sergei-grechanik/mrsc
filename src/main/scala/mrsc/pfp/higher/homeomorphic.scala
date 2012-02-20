package mrsc.pfp.higher

import mrsc.core._
import Higher._

object HHE {
  def he[T](t1: HExpr[T], t2: HExpr[T], n1: Int = 0, n2: Int = 0): Boolean = 
    heByDiving(t1, t2, n1, n2) || heByCoupling(t1, t2, n1, n2)
  
  def heByDiving[T](t1: HExpr[T], t2: HExpr[T], n1: Int = 0, n2: Int = 0): Boolean =  t2 match {
    case HVar(_) => false
    case HAtom(_) => false
    case HErr(_) => false
    case HCtr(c, as) =>
      as.exists(a => he(t1, a, n1, n2))
    case HLambda(b) =>
      he(t1, b, n1, n2 + 1)
    case HFix(h) =>
      he(t1, h, n1, n2)
    case HCall(h, as) =>
      (h :: as).exists(a => he(t1, a, n1, n2))
    case HMatch(e, cs) =>
      he(t1, e, n1, n2) || cs.toList.exists({case (_,(k,b)) => he(t1, b, n1, n2 + k)})
  }
    
  def heByCoupling[T](t1: HExpr[T], t2: HExpr[T], n1: Int = 0, n2: Int = 0): Boolean = (t1, t2) match {
	  case (HErr(er1), HErr(er2)) => true 
	  case (HVar(i), HVar(j)) if i - n1 == j - n2 => true
	  case (HVar(i), _) if i < n1 => false
	  case (_, HVar(i)) if i < n2 => false
	  case (_, _) if isVarAtom(t1) && isVarAtom(t2) => true
	  case (HCtr(k1, as1), HCtr(k2, as2)) if k1 == k2 && as1.length == as2.length =>
	    (as1 zip as2).forall({case (a1,a2) => he(a1, a2, n1, n2)})
	  case (HLambda(b1), HLambda(b2)) =>
	    he(b1, b2, n1 + 1, n2 + 1)
	  case (HFix(b1), HFix(b2)) =>
	    he(b1, b2, n1, n2)
	  case (HMatch(x1, cs1), HMatch(x2, cs2))
	  		if cs1.toList.map(p => (p._1, p._2._1)) == cs2.toList.map(p => (p._1, p._2._1)) =>  
	    he(x1, x2, n1, n2) && 
	    (cs1.toList zip cs2.toList).forall( 
	      {case ((c,(k,b1)),(_,(_,b2))) => he(b1, b2, n1 + k, n2 + k)})
	  case (HCall(f1, as1), HCall(f2, as2)) if as1.length == as2.length =>
	    (f1 :: as1 zip f2 :: as2).forall(p => he(p._1, p._2, n1, n2))
	  case (_, _) => false
  }
}