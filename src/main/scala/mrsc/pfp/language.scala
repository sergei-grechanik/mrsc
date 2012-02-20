package mrsc.pfp

import mrsc.core._

trait PFPSyntax[C] {
  def subst(c: C, sub: Subst[C]): C
  def findSubst(from: C, to: C): Option[Subst[C]]
  def rawRebuildings(c: C): List[RawRebuilding[C]]
  def translate(rebuilding: RawRebuilding[C]): C
  def trivialRb(c: C)(rb: RawRebuilding[C]) =
    (rb._2.values.toSet + rb._1) exists { subclass.equiv(c, _) }
  def rebuildings(c: C): List[C] =
    rawRebuildings(c) filterNot trivialRb(c) map translate
  def size(c: C): Int
  val subclass: PartialOrdering[C]
}

trait PFPSemantics[C] {
  def driveStep(c: C): DriveStep[C]
}

trait Residuation[C] {
  def residuate(graph: TGraph[C, DriveInfo[C]]): C
}

trait MutualGens[C] extends PFPSyntax[C] {
  def mutualGens(c1: C, c2: C): List[RawRebuilding[C]] = {
    val nonTrivialRbs = rawRebuildings(c1) filterNot trivialRb(c1)
    nonTrivialRbs filter { rb => subclass.gteq(rb._1, c2) }
  }
}

trait MSG[C] extends MutualGens[C] {
  def msg(c1: C, c2: C): Option[RawRebuilding[C]] = {
    val mutual = mutualGens(c1, c2)
    mutual find { rb => mutual forall { other => subclass.lteq(rb._1, other._1) } }
  }
}

case class Contraction[C](v: Name, pat: C) {
  override def toString =
    if (v != null) v + " = " + pat else ""
  def subst() = Map[Name, C](v -> pat)
}

sealed trait DriveInfo[C] {
}

case class TransientStepInfo[C](hash: Integer = null) extends DriveInfo[C] {
  override def hashCode = if(hash == null) 42 else hash
  override def equals(o: Any): Boolean = o match {
    case ds : TransientStepInfo[C] => ds.hash == hash
    case _ => false
  }
  override def toString = "->"
}

case class VariantsStepInfo[C](contr: Contraction[C]) extends DriveInfo[C] {
  override def toString = contr.toString
}

case class DecomposeStepInfo[C](compose: List[C] => C, hash: Integer = null) extends DriveInfo[C] {
  override def toString = ""
  
  // TODO: It is a crutch, we should use first-order data structures instead.
  override def hashCode = if(hash == null) compose.hashCode() else hash
  override def equals(o: Any): Boolean = o match {
    case ds : DecomposeStepInfo[C] =>
      if(hash == null && ds.hash == null)
        ds.compose == compose
      else
        ds.hash == hash
    case _ => false
  }
}

sealed trait DriveStep[C] {
  val graphStep: GraphRewriteStep[C, DriveInfo[C]]
}

case class StopDriveStep[C] extends DriveStep[C] {
  val graphStep =
    CompleteCurrentNodeStep[C, DriveInfo[C]]()
}

case class TransientDriveStep[C](next: C) extends DriveStep[C] {
  val graphStep = {
    val ns = List((next, TransientStepInfo[C](next.hashCode())))
    AddChildNodesStep[C, DriveInfo[C]](ns)
  }
}

case class DecomposeDriveStep[C](compose: List[C] => C, parts: List[C]) extends DriveStep[C] {
  val graphStep = {
    val ns = parts map { (_, DecomposeStepInfo(compose, hashCode)) }
    AddChildNodesStep[C, DriveInfo[C]](ns)
  }
  
  // We may need this kind of equality but I'm not sure.
  override def equals(o: Any): Boolean = o match {
    case ds : DecomposeDriveStep[C] => ds.parts == parts && ds.compose(ds.parts) == compose(parts)
    case _ => false
  }
  
  override def hashCode = (compose(parts) :: parts).hashCode
}

case class VariantsDriveStep[C](cases: List[(C, Contraction[C])]) extends DriveStep[C] {
  val graphStep = {
    val ns = cases map { v => (v._1, VariantsStepInfo(v._2)) }
    AddChildNodesStep[C, DriveInfo[C]](ns)
  }
}