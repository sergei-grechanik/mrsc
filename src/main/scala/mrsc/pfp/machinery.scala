package mrsc.pfp

import mrsc.core._

sealed abstract class Extra[+C]
case object NoExtra extends Extra[Nothing]
final case class RebuildingInfo[C](from: C) extends Extra[C]

case class Contraction[+C](v: Name, pat: C) {
  override def toString =
    if (v != null) v + " = " + pat else ""
  def subst() = Map[Name, C](v -> pat)
}

sealed trait DriveInfo[+C]
case object TransientStepInfo extends DriveInfo[Nothing] {
  override def toString = "->"
}
case class DecomposeStepInfo[C](compose: List[C] => C) extends DriveInfo[C] {
  override def toString = ""
}
case class VariantsStepInfo[C](contr: Contraction[C]) extends DriveInfo[C] {
  override def toString = contr.toString
}

sealed trait DriveStep[C] {
  val graphStep: GraphStep[C, DriveInfo[C]]
}

case class TransientDriveStep[C](next: C) extends DriveStep[C] {
  val graphStep = {
    val subSteps = List((next, TransientStepInfo)): List[(C, DriveInfo[C])]
    AddChildNodesStep(subSteps)
  }
}

case class StopDriveStep[C] extends DriveStep[C] {
  val graphStep: GraphStep[C, DriveInfo[C]] =
    CompleteCurrentNodeStep()
}

case class DecomposeDriveStep[C](compose: List[C] => C, parts: List[C]) extends DriveStep[C] {
  val graphStep: GraphStep[C, DriveInfo[C]] = {
    val stepInfo = DecomposeStepInfo(compose)
    val subSteps = parts map { a => (a, stepInfo) }
    AddChildNodesStep(subSteps)
  }
}

case class VariantsDriveStep[C](cases: List[(C, Contraction[C])]) extends DriveStep[C] {
  val graphStep: GraphStep[C, DriveInfo[C]] = {
    val ns = cases map { v => (v._1, VariantsStepInfo(v._2)) }
    AddChildNodesStep(ns)
  }
}

trait PFPMachine[C] extends Machine[C, DriveInfo[C]] {

  type N = Node[C, DriveInfo[C]]
  type Warning
  def canFold(g: G): Option[N]
  def drive(g: G): List[S]
  def rebuildings(whistle: Option[Warning], g: G): List[S]
  def mayDiverge(g: G): Option[Warning]

  override def steps(g: G): List[S] =
    canFold(g) match {
      case Some(node) =>
        List(FoldStep(node))
      case _ =>
        val whistle = mayDiverge(g)
        val driveSteps = if (whistle.isEmpty) drive(g) else List()
        val rebuildSteps = rebuildings(whistle, g)
        rebuildSteps ++ driveSteps
    }
}

trait Driving[C] extends PFPMachine[C] with PFPSemantics[C] {
  override def drive(g: G): List[S] = List(driveConf(g.current.conf).graphStep)
}

trait RenamingFolding[C] extends PFPMachine[C] with PFPSyntax[C] {
  override def canFold(g: G): Option[N] =
    g.current.ancestors.find { n => subclass.equiv(g.current.conf, n.conf) }
}

trait BinaryWhistle[C] extends PFPMachine[C] {
  type Warning = N
  val ordering: PartialOrdering[C]
  override def mayDiverge(g: G): Option[Warning] =
    g.current.ancestors find { n => ordering.lteq(n.conf, g.current.conf) }
}

trait UnaryWhistle[C] extends PFPMachine[C] {
  type Warning = Unit
  def dangerous(c: C): Boolean
  override def mayDiverge(g: G): Option[Warning] =
    if (dangerous(g.current.conf)) Some(Unit) else None
}

trait AllRebuildings[C] extends PFPMachine[C] with PFPSyntax[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] = {
    rebuildings(g.current.conf) map { RebuildStep(_): S }
  }
}

trait LowerRebuildingsOnBinaryWhistle[C] extends PFPMachine[C] with PFPSyntax[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None    => List()
      case Some(_) => rebuildings(g.current.conf) map { RebuildStep(_): S }
    }
}

trait UpperRebuildingsOnBinaryWhistle[C] extends PFPMachine[C] with PFPSyntax[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None        => List()
      case Some(upper) => rebuildings(upper.conf) map { RollbackStep(upper, _) }
    }
}

trait DoubleRebuildingsOnBinaryWhistle[C] extends PFPMachine[C] with PFPSyntax[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None =>
        List()
      case Some(upper) =>
        val rebuilds: List[S] =
          rebuildings(g.current.conf) map { RebuildStep(_): S }
        val rollbacks: List[S] =
          rebuildings(upper.conf) map { RollbackStep(upper, _) }
        rollbacks ++ rebuilds
    }
}

trait LowerAllBinaryGensOnBinaryWhistle[C] extends PFPMachine[C] with MutualGens[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None => List()
      case Some(upper) =>
        mutualGens(g.current.conf, upper.conf) map translate map { RebuildStep(_): S }
    }
}

trait UpperAllBinaryGensOnBinaryWhistle[C] extends PFPMachine[C] with MutualGens[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None => List()
      case Some(upper) =>
        mutualGens(upper.conf, g.current.conf) map translate map { RollbackStep(upper, _) }
    }
}

trait DoubleAllBinaryGensOnBinaryWhistle[C] extends PFPMachine[C] with MutualGens[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None =>
        List()
      case Some(upper) =>
        val rollbacks: List[S] = mutualGens(upper.conf, g.current.conf) map translate map { RollbackStep(upper, _) }
        val rebuilds: List[S] = mutualGens(g.current.conf, upper.conf) map translate map { RebuildStep(_): S }
        rollbacks ++ rebuilds
    }
}

trait LowerAllBinaryGensOrDriveOnBinaryWhistle[C] extends PFPMachine[C] with MutualGens[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None => List()
      case Some(upper) =>
        val rebuilds: List[S] = mutualGens(g.current.conf, upper.conf) map translate map { RebuildStep(_): S }
        if (rebuilds.isEmpty) {
          drive(g)
        } else {
          rebuilds
        }
    }
}

trait UpperAllBinaryGensOrDriveOnBinaryWhistle[C] extends PFPMachine[C] with MutualGens[C] with BinaryWhistle[C] {
  override def rebuildings(whistle: Option[Warning], g: G): List[S] =
    whistle match {
      case None => List()
      case Some(upper) =>
        val rollbacks = mutualGens(upper.conf, g.current.conf) map translate map { RollbackStep(upper, _) }
        if (rollbacks.isEmpty) {
          drive(g)
        } else {
          rollbacks
        }
    }
}

trait UpperMsgOrLowerMggOnBinaryWhistle[C]
  extends PFPMachine[C] with MSG[C] with BinaryWhistle[C] {

  def rebuildings(whistle: Option[Warning], g: G): List[S] = {
    whistle match {
      case Some(upper) =>
        val currentConf = g.current.conf
        val upperConf = upper.conf
        msg(upperConf, currentConf) match {
          case Some(rb) =>
            val conf1 = translate(rb)
            List(RollbackStep(upper, conf1))
          case None =>
            val cands = rawRebuildings(currentConf) filterNot trivialRb(currentConf)
            val mgg = cands find { case (c1, _) => cands forall { case (c2, _) => subclass.lteq(c2, c1) } }
            mgg.map(translate).map(RebuildStep(_): S).toList
        }
      case None =>
        List()
    }
  }
}

// funny: most specific down or most general up
trait LowerMsgOrUpperMggOnBinaryWhistle[C] extends PFPMachine[C] with MSG[C] with BinaryWhistle[C] {

  def rebuildings(whistle: Option[Warning], g: G): List[S] = {
    whistle match {
      case Some(upper) =>
        val currentConf = g.current.conf
        val upperConf = upper.conf
        msg(currentConf, upperConf) match {
          case Some(rb) =>
            val conf1 = translate(rb)
            val replace = RebuildStep(conf1): S
            List(replace)
          case None =>
            val cands = rawRebuildings(upperConf) filterNot trivialRb(upperConf)
            val mgg = cands find { case (c1, _) => cands forall { case (c2, _) => subclass.lteq(c2, c1) } }
            mgg.map(translate).map(RollbackStep(upper, _)).toList
        }
      case None =>
        List()
    }
  }
}

trait MSGCurrentOrDriving[C] extends PFPMachine[C] with MSG[C] with BinaryWhistle[C] {

  def rebuildings(whistle: Option[Warning], g: G): List[S] = {
    whistle match {
      case Some(upper) =>
        val currentConf = g.current.conf
        val upperConf = upper.conf
        msg(currentConf, upperConf) match {
          case Some(rb) =>
            val conf1 = translate(rb)
            val replace: S = RebuildStep(conf1)
            List(replace)
          case None =>
            drive(g)
        }
      case None =>
        List()
    }
  }
}

trait DoubleMsgOnBinaryWhistle[C] extends PFPMachine[C] with MSG[C] with BinaryWhistle[C] {

  def rebuildings(whistle: Option[Warning], g: G): List[S] = {
    whistle match {
      case Some(upper) =>
        val current = g.current
        val rollbacks = msg(upper.conf, current.conf) map { rb => RollbackStep(upper, translate(rb)) }
        val rebuildings = msg(current.conf, upper.conf) map { rb => RebuildStep(translate(rb)): S }
        rollbacks.toList ++ rebuildings.toList
      case None =>
        List()
    }
  }
}