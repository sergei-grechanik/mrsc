package mrsc.pfp.higher

import mrsc.core._
import mrsc.pfp._
import Higher._

trait HigherSemantics[T] extends PFPSemantics[HExpr[T]] {
  
  protected val doNormalization = true
  
  type C = HExpr[T]
  def driveStep(c: C): DriveStep[C] = {
    def norm[U](e: HExpr[U]): HExpr[U] = 
      if(doNormalization) normalize(e) else e
    
    if(isWHNF(c)) {
      // If c is in WHNF, we should peel off top-level lambdas and constructors. 
      val (fun,newcs) = peel(c)
      if(newcs.isEmpty)
        // All kinds of drive steps are essentially DecomposeDriveSteps
        // with different compose functions.
        StopDriveStep()
      else
	    DecomposeDriveStep(unpeel(fun, _), newcs)
    }
    else {
      // Decompose c into context and a redex.
      val (fun,redex) = decompose(c)
      redex match {
        case HFix(h) =>
          TransientDriveStep(norm(compose(fun, List(HCall(h, List(redex))))))
          
        case HMatch(x, csmap) if isVarAtom(x) =>
          val cs = csmap.toList
          // xvals is a list of possible values of x (of the form C x1 x2 .. xn)
          val xvals = cs map {case (c,(n,_)) => HCtr(c, (0 to n - 1).toList map (i => HVar(i)))}
          // put the cases' bodies into the context
          val preconfs = cs map {case (c,(n,b)) => (n, compose(mapVar(i => HVar(i + n))(fun), List(b)))}
          // if x is a variable, it has changed its number 
          def newx(n: Int) = x match {
            case HVar(i) => HVar(i + n)
            case _ => x
          }
          // propagate positive information
          val confs = preconfs zip xvals map {case ((n, c), xv) => norm(replaceVarAtom(newx(n), xv)(c)) }
          
          DecomposeDriveStep((l => HMatch(x, (cs zip l).map({case ((c,(n,_)),y) => (c, (n, y))}).toMap)), confs)
          
        case HCall(f, as) if isVarAtom(f) =>
          if(fun == HAtom(Left(0))) {
            // We can do no better than to split our function call.
            DecomposeDriveStep(HCall(f, _), as)
          }
          else {
            // Here we can split our expression into a context and a function call.
            // TODO: There may be several occurrences of f in c, so we could factor out all of them.
            val fun1 = compose(mapVar(i => HVar(i + 1))(fun), List(HVar(0)))
            DecomposeDriveStep((l => applyN(l(0), List(l(1)))), List(fun1, redex))
          }
            
        case _ =>
          TransientDriveStep(normalize(c))
      }
    }
  }
}

object HigherSyntax {
  
  type HSubst[T] = Map[Either[Int, T], HExpr[T]]
  
  def generalize[T](expr1: HExpr[T], expr2: HExpr[T]): HExpr[Either[(HExpr[T], HExpr[T]), T]] = {
    // TODO: There is room for improvement: if we treat branches as proper functions we can
    // get a more specific generalization.
    // case E of { S x y => f x y }
    // case E of { S x y => f y x }
    // case E of { S x y => (f | \x y -> f y x) x y }
    def gen(e1: HExpr[T], e2: HExpr[T], n: Int): Option[HExpr[Either[(HExpr[T], HExpr[T]), T]]] = {
      // We try to find a generalization by matching the expressions
      val guess = (e1,e2) match {
	      case (HErr(er1), HErr(er2)) => Some(HErr(er1 + " OR " + er2))
	      case (HVar(i), HVar(j)) if i == j => Some(HVar(i))
	      case (HVar(i), HVar(j)) if i < n || j < n => None
	      case (HAtom(a), HAtom(b)) if a == b => Some(HAtom(Right(a)))
	      case (HCtr(n1, as1), HCtr(n2, as2)) if n1 == n2 && as1.length == as2.length =>
	        val genas = (as1 zip as2) map (p => gen(p._1, p._2, n))
	        if(genas.forall(_.isDefined))
	          Some(HCtr(n1, genas map (_.get)))
	        else
	          None
	      case (HLambda(b1), HLambda(b2)) =>
	        gen(b1, b2, n + 1).map(HLambda(_))
	      case (HFix(b1), HFix(b2)) =>
	        gen(b1, b2, n).map(HFix(_))
	      case (HMatch(x1, cs1), HMatch(x2, cs2))
	      		if cs1.toList.map(p => (p._1, p._2._1)) == cs2.toList.map(p => (p._1, p._2._1)) =>
	        val x = gen(x1, x2, n)
	        val gencs = 
	          (cs1.toList zip cs2.toList) map 
	          {case ((c,(k,b1)),(_,(_,b2))) => gen(b1, b2, n + k) map (b => (c, (k,b)))}
	        if(x.isDefined && gencs.forall(_.isDefined))
	          Some(HMatch(x.get, gencs.map(_.get).toMap))
	        else
	          None
	      case (HCall(f1, as1), HCall(f2, as2)) if as1.length == as2.length =>
	        val genas = (f1 :: as1 zip f2 :: as2) map (p => gen(p._1, p._2, n))
	        if(genas.forall(_.isDefined))
	          Some(HCall(genas.head.get, genas.tail map (_.get)))
	        else
	          None
	      case (_, _) => None
      }
      
      // If we failed to find a generalization then we might be able to 
      // factor out these expressions if they don't contain bound variables.
      if(guess.isDefined)
        guess
      else
        try {
        	val ne1 = mapVar(i => if(i >= n) HVar(i - n) else throw new Exception)(e1)
			val ne2 = mapVar(i => if(i >= n) HVar(i - n) else throw new Exception)(e2)
			Some(HAtom(Left((ne1,ne2))))
        }
        catch {
          case _ => None
        }
    }
    
    gen(expr1, expr2, 0).get
  }
  
  def findSubst[T](from: HExpr[T], to: HExpr[T]): Option[HSubst[T]] = {
    val gen = generalize(from, to)
    
    var sub = Map[Either[Int,T], HExpr[T]]()
    
    def add(i: Either[Int, T], e: HExpr[T]) {
      if(sub.contains(i)) {
        if(sub.get(i).get != e) {          
          throw new Exception
        }
      }
      else
        sub += Pair(i, e)
    }
    
    try {
    	// TODO: mapAll should be replaced with something appropriate here
	    mapAll((x: Either[Int, Either[(HExpr[T], HExpr[T]), T]]) => x match {
	      case Left(i) => add(Left(i), HVar(i)); HErr("")
	      case Right(Right(a)) => add(Right(a), HAtom(a)); HErr("")
	      case Right(Left((HVar(i), b))) => add(Left(i), b); HErr("")
	      case Right(Left((HAtom(a), b))) => add(Right(a), b); HErr("")
	      case Right(Left(g)) =>
	        throw new Exception
	    })(gen)
	    
	    Some(sub)
    }
	catch {
	  case _ => None
	}
  }
  
  def equiv[T](e1: HExpr[T], e2: HExpr[T]): Boolean = instanceOf(e1, e2) && instanceOf(e2, e1)
  def instanceOf[T](e1: HExpr[T], e2: HExpr[T]): Boolean = findSubst(e1, e2).isDefined
  
  def subst[T](c: HExpr[T], sub: HSubst[T]): HExpr[T] = mapAll(sub)(c)
}

import HigherSyntax._

case class HigherResiduator[T](
    pathToT: TPath => T,
    findSubstFunction: (HExpr[T], HExpr[T]) => Option[HSubst[T]] = HigherSyntax.findSubst[T] _) 
	extends Residuation[HExpr[T]] {
  
  def residuate(graph: TGraph[HExpr[T], DriveInfo[HExpr[T]]]): HExpr[T] = {
    
    def fold(n: TNode[HExpr[T], DriveInfo[HExpr[T]]]): HExpr[T] = n.base match {
      case Some(path) =>
        val fnode = graph.get(path)
        val sub = findSubstFunction(fnode.conf, n.conf).get
        val as = sub.toList map (_._2)
        val res = if (as.isEmpty)
          HAtom(pathToT(path))
        else
          HCall(HAtom(pathToT(path)), as)
          
//        println("")
//        println(n.conf)
//        println("===>")
//        println(res)
//        println("same thing as")
//        println(fnode.conf)
//        println(sub)
//        println("")
          
        res
      case None =>
        val expr = n.outs match {
          case Nil => n.conf
          case chld => chld.head.driveInfo match {
            case TransientStepInfo() => fold(chld.head.node)
            case DecomposeStepInfo(comp) => comp(chld map (c => fold(c.node)))
          }
        }
        
//        println("")
//        println(n.conf)
//        println("===>")
//        println(expr)
//        println("")
        
        if(graph.leaves.exists { _.base == Some(n.tPath) }) {
          val unbnd = unboundList(n.conf).reverse
          val corr = unbnd zip (0 to unbnd.size - 1)
          val corr1 = corr ++ List((Right(pathToT(n.tPath)), unbnd.size))
          val closed = mapAll((a:Either[Int,T]) => corr1.toMap.mapValues(HVar(_)).get(a).getOrElse(fromEither(a)))(expr)
          val res = HCall(HFix(hlambdas(closed, corr1.length)), corr.map(_._1.fold(HVar(_), HAtom(_))).reverse)
//          println("after folding:")
//          println(res)
//          println("")
          res
        }
        else
          expr
    }
    
    fold(graph.root)
  }
}
