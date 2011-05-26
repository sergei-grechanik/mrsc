package mrsc

/*!# Abstract machines
  
  An abstract machine represents the semantics of the object language 
  (more precisely, meta-semantics) through operations over SC graphs. 
  `SingleResultMachine` corresponds to a classical (= deterministic) supercompiler,
  while `MultiResultMachine` corresponds to a novel (= non-deterministic) supercompiler.
 */

trait SingleResultMachine[C, D, E] {
  def makeStep(pState: PState[C, D, E]): MStep[C, D, E]
}

trait MultiResultMachine[C, D, E] {
  def makeSteps(pState: PState[C, D, E]): List[MStep[C, D, E]]
}

/*!# Abstract steps
  
 Under the hood an abstract machine deals with some kind of semantics of the language.
 Low-level operations should be translated into high-level abstract operations (or messages) 
 over SC graphs.
 */
sealed trait MStep[+C, +D, +E]

/*! The step `MMakeLeaf` means that the current branch of the graph in focus is
   a terminal node (leaf).
 */
case object MMakeLeaf extends MStep[Nothing, Nothing, Nothing]

/*! The step `MPrune` means that the current graph should be discarded. In the case of 
 the "single-result" supercompilation it means failure (= no good result). In the case of
 multi-result supercompilation it means that we should continue with the next variant.   
 */
case object MPrune extends MStep[Nothing, Nothing, Nothing]

/*! `MAddForest` corresponds to development of current branch of the graph (driving in 90%).
 Development is divided into several `subSteps`.
 */
case class MAddForest[+C, +D, +E](val subSteps: List[SubStep[C, D, E]]) extends MStep[C, D, E]

/*! `MReplace` is fixing the current state of the branch.
 */
case class MReplace[C, D, E](val conf: C, val extraInfo: E) extends MStep[C, D, E]

/*! `MRollback` is fixing the past `dangerous` state of the current branch.
 */
case class MRollback[C, D, E](val dangerous: CoNode[C, D, E],
  val safe: C, val extra: E) extends MStep[C, D, E]

/*! `MFold` signals that there is a path to something similar to the current state in the past
 of the current SC Graph.
 */
case class MFold(val path: Path) extends MStep[Nothing, Nothing, Nothing]

/* Usually `SubStep` hides internals of driving.  */
case class SubStep[+C, +D, +E](label: C, info: D, extra: E)

/*!# Processing of complete graphs
 
 Graph builder knows only how to build a graph, but not what to do with this graph later.
 Processing of complete SC graphs is extracted into a separate abstraction.
 */

/*! An instance of a graph may be pruned, and a client may be interested in knowing that fact:
  so `GraphConsumer` receives `Some(graph)` when graph is completed and receives `None` 
  if the graph was pruned. 
 */
trait CoGraphConsumer[C, D, E] {
  val description: String
  def consume(graph: Option[CoGraph[C, D, E]]): Unit
}

/*!# Modeling expectations
 */

/*! The following exception usually means that some modeling expectation (or hypothesis) 
 was not met during actual modeling.  
 */
class ModelingError(val message: String) extends Exception(message: String)

/*!# Whistle and tricks
  
 `GenericMultiMachine` is well suited for implementing different aspects in traits.
  
 It turns out that "pure" multi-result supercompilation is limited by whistle only. 
 "Advanced" (such as two-level) multi-result supercompilation is limited by additional tricks 
 (such as improvement lemma) applied during supercompilation. 
  
 So `W` here stands for "whistle signal".
*/
trait GenericMultiMachine[C, D, E, W] extends MultiResultMachine[C, D, E] {

  def isLeaf(pState: PState[C, D, E]): Boolean
  def fold(pState: PState[C, D, E]): Option[Path]
  def blame(pState: PState[C, D, E]): W
  def drive(whistle: W, pState: PState[C, D, E]): List[MStep[C, D, E]]
  def rebuildings(whistle: W, pState: PState[C, D, E]): List[MStep[C, D, E]]
  def tricks(whistle: W, pState: PState[C, D, E]): List[MStep[C, D, E]]

  /*! The logic of this machine is straightforward:
     
     * If there are opportunities for folding, lets fold.
     
     * Otherwise, lets try all variants.
    
   Note that the whistle signal is passed to `drive`, `rebuildings` and `tricks`.
  */
  override def makeSteps(pState: PState[C, D, E]): List[MStep[C, D, E]] =
    if (isLeaf(pState))
      List(MMakeLeaf)
    else fold(pState) match {
      case Some(path) =>
        List(MFold(path))
      case _ =>
        val signal = blame(pState)
        val driveSteps = drive(signal, pState)
        val genSteps = rebuildings(signal, pState)
        val trickySteps = tricks(signal, pState)
        driveSteps ++ (trickySteps ++ genSteps)
    }
}