package mrsc.pfp.samples

import mrsc.core._
import mrsc.pfp._

case class AllMSC(val gc: GContext) extends PFPRules
  with PFPSyntax
  with PFPSemantics
  with Driving
  with AllFoldingCandidates
  with Folding
  with AllEmbeddingCandidates
  with HEWhistle
  with AllRebuildings

object AllMSC extends SC

// All rebuildings but only on whistle
case class MSC1(val gc: GContext) extends PFPRules
  with PFPSyntax
  with PFPSemantics
  with Driving
  with AllFoldingCandidates
  with Folding
  with AllEmbeddingCandidates
  with HEWhistle
  with LowerRebuildingsOnBinaryWhistle

object MSC1 extends SC

case class MSC2(val gc: GContext) extends PFPRules
  with PFPSyntax
  with PFPSemantics
  with Driving
  with AllFoldingCandidates
  with Folding
  with AllEmbeddingCandidates
  with HEWhistle
  with LowerAllBinaryGensOnBinaryWhistle

object MSC2 extends SC

case class MSC3(val gc: GContext) extends PFPRules
  with PFPSyntax
  with PFPSemantics
  with Driving
  with AllFoldingCandidates
  with Folding
  with AllEmbeddingCandidates
  with HEByCouplingWhistle
  with LowerAllBinaryGensOnBinaryWhistle

object MSC3 extends SC

case class MSC4(val gc: GContext) extends PFPRules
  with PFPSyntax
  with PFPSemantics
  with Driving
  with AllFoldingCandidates
  with Folding
  with AllEmbeddingCandidates
  with HEByCouplingWhistle
  with UpperAllBinaryGensOnBinaryWhistle

object MSC4 extends SC

