package mrsc.pfp.higher

import scala.collection.mutable.WrappedArray
import scala.util.parsing.combinator.ImplicitConversions
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.{CharSequenceReader => Reader}

object HigherGlobals {
  private val md = java.security.MessageDigest.getInstance("SHA-1")
  private val encoder = new sun.misc.BASE64Encoder()

  var hash2name: Map[WrappedArray[Byte], String] = Map()
  var name2expr: Map[String, HExpr[Any]] = Map()
  
  def add(n: String, e: HExpr[Any]) {
    hash2name += Pair(e.hash, n)
    name2expr += Pair(n, e)
  }
  
  def getByName[T](n: String): HExpr[T] = {
    import Higher._
    mapVal[Any,T]((x:Any) => throw new Exception)(name2expr(n))
  }
  
  def hash(o: Any): WrappedArray[Byte] = {
    md.digest(o.toString().getBytes)
  }
  
  def hash2str(h: WrappedArray[Byte], n: Int = 9): String =
    encoder.encode(h.toArray).take(9).replaceAll("[^a-zA-Z0-9_]", "")
  
}

sealed trait HExpr[+T] {
  def toStringSimple: String
  lazy val hash = HigherGlobals.hash(toStringSimple)
  def hashName: String = HigherGlobals.hash2str(hash)
  
  protected def toString1: String
  
  override def toString = HigherGlobals.hash2name.getOrElse(hash, toString1)
  
  protected def indent(s: String): String = "  " + s.replace("\n", "\n  ")
}

case class HAtom[T](value: T) extends HExpr[T] {
  override def toStringSimple = "[" + value.toString() + "]"
  override def toString1 = value.toString()
}

// Variables are represented by de Bruijn indices.
case class HVar[T](index: Int) extends HExpr[T] {
  override def toStringSimple = index.toString()
  override def toString1 = toStringSimple
}

case class HLambda[T](body: HExpr[T]) extends HExpr[T] {
  override def toStringSimple = "(\\ " + body.toStringSimple + ")"
  override def toString1 = {
    import Higher._
    val varname = "v" + body.hashName
    "(\\" + varname + " ->\n" + indent(apply(HLambda(mapVal((x:T) => x.toString)(body)), HAtom(varname)).toString) + "\n)"
  }
}

case class HCall[T](fun: HExpr[T], args: List[HExpr[T]]) extends HExpr[T] {
  override def toStringSimple = 
    "(" + fun.toStringSimple + args.map(_.toStringSimple).mkString(" ", " ", "") + ")"
  override def toString1 = 
    "(" + fun.toString + args.mkString(" ", " ", "") + ")"  
}

case class HCtr[T](name: String, args: List[HExpr[T]]) extends HExpr[T] {
  override def toStringSimple = "(" + name + args.map(_.toStringSimple).mkString(" ", " ", "") + ")"
  override def toString1 = 
    "(" + name + args.mkString(" ", " ", "") + ")"
}

// Cases are triples (Constructor name, n = Number of args, body).
// Fisrt n vars in a body are considered bound by the case clause.
case class HMatch[T](expr: HExpr[T], cases: Map[String, (Int, HExpr[T])]) extends HExpr[T] {
  override def toStringSimple = 
    "case " + expr.toStringSimple + " of " + 
    cases.toList.map({case (c, (n,b)) => c + " " + n + " -> " + b.toStringSimple}).mkString("{", "; ", "}")
  override def toString1 = {
    import Higher._
    val scases = for((c, (n, b)) <- cases) yield {
      val varnames = (for(i <- 0 to n - 1) yield "v" + b.hashName + "_" + i).toList
      var bodystr = applyN(mapVal((x:T) => x.toString)(b), varnames map (HAtom(_))).toString
      if(bodystr.contains("\n"))
        bodystr = "\n" + indent(bodystr)
      indent(c + varnames.mkString(" ", " ", "") + " -> " + bodystr + ";")
    }
    "case " + expr.toString + " of " + scases.mkString("{\n", "\n", "\n}")
  }
}

case class HFix[T](fun: HExpr[T]) extends HExpr[T] {
  override def toStringSimple = "(Y " + fun.toStringSimple + ")"
  override def toString1 = "(Y " + fun.toString + ")"
}

case class HErr[T](err: String) extends HExpr[T] {
  override def toStringSimple = "(Error: " + err + ")"
  override def toString1 = toStringSimple
}

//case class HLet[T](fun: HExpr[T], args: List[HExpr[T]]) extends HExpr[T] {
//  override def toString = "{" + fun.toString() + args.mkString(" ", " ", " ") + "}"
//}

object Higher {
  private def liftvar[T](e: Either[Int, T]): HExpr[T] = e match {
    case Left(i) => HVar(i + 1)
    case Right(a) => HAtom(a)
  }
  
  def mapAll[T,U](f: Either[Int, T] => HExpr[U])(expr: HExpr[T]): HExpr[U] = expr match {
    case HVar(i) => f(Left(i))
    case HAtom(a) => f(Right(a))
    case HErr(e) => HErr(e)
    case HCall(h,as) => HCall(mapAll(f)(h), as map mapAll(f))
    case HCtr(c,as) => HCtr(c, as map mapAll(f)) 
    case HMatch(e, cs) =>
      val f1 = mapVal((x:U) => Right(x)) compose f
      val newf = (n : Int) => (x : Either[Int, T]) => x match {
        case Left(i) =>
      	  if(i >= n)
      	    mapVar(i => HVar(i + n))(f(Left(i-n)))
      	  else
      	    HVar(i)
      	case Right(a) =>
      	  mapVar(i => HVar(i + n))(f(Right(a)))
      }
      HMatch(mapAll(f)(e), cs map {case (c,(n,h)) => (c,(n, mapAll(newf(n))(h)))})
    case HFix(h) => HFix(mapAll(f)(h))
    //case HLet(h,as) => HLet(mapAll(f)(h), as map mapAll(f))
    case HLambda(b) =>
      HLambda(mapAll[T,U]({x : Either[Int,T] => x match {
      	case Left(i) =>
      	  if(i >= 1)
      	    mapAll(liftvar[U])(f(Left(i-1)))
      	  else
      	    HVar(i)
      	case Right(a) =>
      	  mapAll(liftvar[U])(f(Right(a)))
  	  }})(b))
  }
  
  def mapVar[T](f: Int => HExpr[T]): HExpr[T] => HExpr[T] =
    mapAll[T,T]({x => x match {
      	case Left(i) => f(i)
      	case Right(a) => HAtom(a)
      }})
      
  def mapAtom[T,U](f: T => HExpr[U]): HExpr[T] => HExpr[U] =
    mapAll[T,U]({x => x match {
      	case Left(i) => HVar(i)
      	case Right(a) => f(a)
      }})
      
  def mapVal[T,U](f: T => U): HExpr[T] => HExpr[U] =
    mapAtom(x => HAtom(f(x)))
      
  def apply[T](f: HLambda[T], a: HExpr[T]): HExpr[T] = 
    mapVar[T](i => if(i == 0) a else HVar(i - 1))(f.body)
  
  def applyN[T](body: HExpr[T], as: List[HExpr[T]]): HExpr[T] = 
    mapVar[T](i => if(i < as.length) as(as.length - i - 1) else HVar(i - as.length))(body)
  
  def hlambdas[T](expr: HExpr[T], n: Int): HExpr[T] =
    if(n == 0) expr else hlambdas(HLambda(expr), n - 1)
    
  def normalize[T](expr: HExpr[T]): HExpr[T] = expr match {
    case HVar(_) => expr
    case HAtom(_) => expr
    case HErr(_) => expr
    case HCtr(c, as) => HCtr(c, as map normalize)
    case HLambda(b) =>
      val nb = normalize(b)
      // eta reduction
      nb match {
        case HCall(h, as) if as.last == HVar(0) =>
          // as cannot be empty due to normalization
          val almost = if(as.length == 1) h else HCall(h, as.init)
          // we should check if it's the only occurrence of 0 and adjust indices
          if(unbound(almost).contains(Left(0)))
            HLambda(nb)
          else
            mapVar(i => HVar(i - 1))(almost)
        case _ => HLambda(nb)
      }
    case HFix(h) => HFix(normalize(h))
    case HCall(h, as) =>
      val hn = normalize(h)
      if(as.isEmpty)
        hn
      else hn match {
        case l@HLambda(hb) => normalize(HCall(apply(l, normalize(as.head)), as.tail))
        case HCtr(n, _) => HErr("cannot call " + n + "(...)")
        case HErr(_) => hn
        case HCall(h1, l1) => HCall(h1, l1 ++ as map normalize)
        case _ => HCall(hn, as map normalize)
      }
    case HMatch(e, cs) => 
      val he = normalize(e)
      he match {
        case HCtr(name, as) =>
          cs.get(name) match {
            case Some((n,fun)) if n == as.length => normalize(applyN(fun, as)) 
            case None => HErr("there is no case for " + name)
          }
        case HErr(_) => expr
        case HLambda(_) => HErr("cannot match against a function")
        case _ => HMatch(he, cs mapValues {case (n,h) => (n, normalize(h))})
      }
  }
  
  def isWHNF[T](expr: HExpr[T]): Boolean = expr match {
    case HVar(_) => true
    case HAtom(_) => true
    case HErr(_) => true
    case HCtr(c, as) => true
    case HLambda(b) => true
    case HFix(h) => false
    case HCall(h, as) => false
    case HMatch(e, cs) => false
  }
  
  def isVarAtom[T](expr: HExpr[T]): Boolean = expr match {
    case HVar(_) => true
    case HAtom(_) => true
    case HErr(_) => false
    case HCtr(c, as) => false
    case HLambda(b) => false
    case HFix(h) => false
    case HCall(h, as) => false
    case HMatch(e, cs) => false
  }
  
  def peel[T](expr: HExpr[T]): (HExpr[Either[Int, T]], List[HExpr[T]]) = {
	  var n = 0
	  var list : List[HExpr[T]] = List()
	  
	  def add(e: HExpr[T]): HExpr[Either[Int, T]] = {
	      list = e :: list
	      n += 1
	      HAtom(Left(n-1))
	  }
	  
	  def peel1(expr: HExpr[T]): HExpr[Either[Int, T]] = expr match {
	    case HVar(i) => HVar(i)
	    case HAtom(a) => HAtom(Right(a))
	    case HErr(e) => HErr(e)
	    case HCtr(c, as) => HCtr(c, as map peel1)
	    case HLambda(b) => HLambda(peel1(b))
	    case HFix(h) => add(expr)
	    case HCall(h, as) => add(expr)
	    case HMatch(e, cs) => add(expr)
	  }
	  
	  val res = peel1(expr)
	  return (res, list.reverse)
  }
  
  def unpeel[T](fun: HExpr[Either[Int, T]], as: List[HExpr[T]]): HExpr[T] = fun match {
    case HVar(i) => HVar(i)
    case HAtom(Left(i)) => as(i)
    case HAtom(Right(a)) => HAtom(a)
    case HErr(e) => HErr(e)
    case HCtr(c, args) => HCtr(c, args map (unpeel(_, as)))
    case HLambda(b) => HLambda(unpeel(b, as))
    case HFix(h) => HFix(unpeel(h, as))
    case HCall(h, args) => HCall(unpeel(h, as), args map (unpeel(_, as)))
    case HMatch(e, cs) => HMatch(unpeel(e, as), cs.mapValues({case (n,b) => (n, unpeel(b,as))}))
  }
  
  def decompose[T](expr: HExpr[T]): (HExpr[Either[Int, T]], HExpr[T]) = expr match {
    case HCall(h, as) if !isWHNF(h) =>
      val (h1,e1) = decompose(h)
      (HCall(h1, as map mapVal(Right(_))), e1)
    case HMatch(h, cs) if !isWHNF(h) =>
      val (h1,e1) = decompose(h)
      (HMatch(h1, cs mapValues {
        	case (n,b) =>
        	  (n, mapVal((v:T) => Right(v))(b))
        }), e1)
    case _ => (HAtom(Left(0)), expr)
  }
  
  def compose[T](fun: HExpr[Either[Int, T]], as : List[HExpr[T]]): HExpr[T] =
    mapAtom((e:Either[Int, T]) => e.fold(as(_), HAtom(_)))(fun)
  
  def replaceVarAtom[T](what: HExpr[T], wit: HExpr[T]): HExpr[T] => HExpr[T] = what match {
    case HAtom(a) => mapAtom(x => if(x == a) wit else HAtom(x))
    case HVar(i) => mapVar(j => if(i == j) wit else HVar(j))
  }
    
  def unbound[T](expr: HExpr[T]): Set[Either[Int, T]] = {
    var res: Set[Either[Int, T]] = Set()
    // TODO: mapAll should be replaced with something appropriate here
    mapAll((e:Either[Int, T]) => {res += e; HErr("")})(expr)
    res
  }
  
  // List of unbound variables sorted in order of occurrence. 
  def unboundList[T](expr: HExpr[T]): List[Either[Int, T]] = {
    var set: Set[Either[Int, T]] = Set()
    var res: List[Either[Int, T]] = Nil
    // TODO: mapAll should be replaced with something appropriate here
    mapAll((e:Either[Int, T]) => {
      if(!set.contains(e)) {
        res = e :: res;
        set += e;
      }
      HErr("")
    })(expr)
    res.reverse
  }
  
  def fromEither[T](e: Either[Int, T]): HExpr[T] = e.fold(HVar(_), HAtom(_))
  
  def hsize[T](expr: HExpr[T]): Int = expr match {
    case HVar(_) => 1
    case HAtom(_) => 1
    case HErr(_) => 1
    case HCtr(c, as) => 1 + as.map(hsize).sum
    case HLambda(b) => 1 + hsize(b)
    case HFix(h) => 1 + hsize(h)
    case HCall(h, as) => 1 + hsize(h) + as.map(hsize).sum
    case HMatch(e, cs) => 1 + hsize(e) + cs.map(x => hsize(x._2._2)).sum
  }
  
  def hdepth[T](expr: HExpr[T]): Int = expr match {
    case HVar(_) => 1
    case HAtom(_) => 1
    case HErr(_) => 1
    case HCtr(c, as) => 1 + (0 :: as.map(hdepth)).max
    case HLambda(b) => 1 + hdepth(b)
    case HFix(h) => 1 + hdepth(h)
    case HCall(h, as) => 1 + (h :: as).map(hdepth).max
    case HMatch(e, cs) => 1 + (hdepth(e) :: cs.map(x => hdepth(x._2._2)).toList).max
  }
}


object HigherParsers extends StandardTokenParsers with ImplicitConversions {
  import Higher._
  
  lexical.delimiters += ("(", ")", "{", "}", "\\", ";", "->")
  lexical.reserved += ("case", "of", "Y")
  
  private def factorVars(vars: List[String], body: HExpr[String]): HExpr[String] =
    mapAtom({(a:String) =>
      		val n = vars.length
  	    	val i = vars.indexOf(a)
  	    	if(i >= 0) HVar(n - i - 1) else HAtom(a)})(mapVar(i => HVar(i + vars.length))(body))
  
  def expr: Parser[HExpr[String]] = lambda | caseof | fix | ctr | call
  
  def fix = "Y" ~> expr ^^ (e => HFix(e))
  
  def call = rep1(vrbl|paren) ^^ 
  	(l => if(l.length == 1) l.head else HCall(l.head, l.tail))
  
  def lambda = ("\\" ~> rep1(name) <~ "->") ~ expr ^^ 
  	{l => 
  	  val names = l._1
  	  var body = factorVars(names, l._2)
  	  for(n <- names)
  	    body = HLambda(body)
  	  body
  	}
  	
  def caseof = ("case" ~> expr <~ "of") ~ ("{" ~> rep(cas <~ ";") <~ "}") ^^
    (l => HMatch(l._1, l._2.toMap))
  
  def cas = ctrname ~ (rep(name) <~ "->") ~ expr ^^
  	{l =>
  	  val body = l._2
  	  val c = l._1._1
  	  val vars = l._1._2
  	  (c, (vars.length, factorVars(vars, body)))
  	}
  
  def ctr = ctrname ~ rep(vrbl|paren) ^^ (p => HCtr(p._1, p._2))
  def paren = "(" ~> expr <~ ")"
  
  def vrbl = name ^^ (HAtom(_))
  def name = ident ^? {case id if id.charAt(0).isLower => id}
  def ctrname = ident ^? {case id if id.charAt(0).isUpper => id}
  
  def parseProg(s: String) = parseExpr(s)
  def parseExpr(s: String) = expr(new lexical.Scanner(new Reader(s))).get
}

