package util

import java.io.{File, PrintWriter}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * A CDCL event that chooses a literal.
  */
sealed trait Event {

  protected val graph: ImplicationGraph

  /**
    * What clauses and literals were disabled as an effect of this event?
    */
  val effects: ArrayBuffer[Effect] = new mutable.ArrayBuffer[Effect]()

  /**
    * The chosen literal.
    */
  def getLiteral: graph.formula.Literal

  /**
    * Register that the clause was disabled because one of its literals became true.
    * @param index – The index of the disabled clause.
    */
  def registerDisabledClause(index: Int): Unit = {
    effects.append(graph.DisableClause(index))
  }

  /**
    * Register that the literal was disabled because it became false.
    * @param clauseIndex – The index of the clause to which the literal belongs.
    * @param literalIndex – The index of the literal inside the clause.
    */
  def registerDisabledLiteral(clauseIndex: Int, literalIndex: Int): Unit = {
    effects.append(graph.DisableLiteral(clauseIndex, literalIndex))
  }
}

/**
  * What was changed as a consequence of the event?
  */
sealed trait Effect {}

/**
  *
  * @param literalCount – The number of literals in the formula.
  * @param formula – Input formula. Needed only for nice debugging info.
  * @param verbose – Should debug info be printed?
  */
class ImplicationGraph(private val literalCount: Int, val formula: Formula,
                       private val verbose: Boolean = false) {

  import formula.{Literal, Variable}

  // Instances of a nested class can access fields of the outer class.

  /**
    * Clause was disabled because one of its literals became true.
    * @param index – The index of the disabled clause.
    */
  case class DisableClause(index: Int) extends Effect

  /**
    * Literal was disabled because it became false.
    * @param clauseIndex – The index of the clause to which the literal belongs.
    * @param literalIndex – The index of the literal inside the clause.
    */
  case class DisableLiteral(clauseIndex: Int, literalIndex: Int) extends Effect

  sealed trait GraphEvent extends Event {
    override protected val graph: ImplicationGraph = ImplicationGraph.this
  }

  /**
    * Sentinel event guarding the start of the list.
    */
  case class Start() extends GraphEvent {
    override def getLiteral: Literal = throw new AssertionError("Bug!")
  }

  /**
    * Literal chosen by the decision rule.
    * @param literal – The literal that was chosen.
    * @param previousDecision – Previous decision, if any.
    */
  case class Decision(literal: Literal,
                      previousDecision: Option[Literal]) extends GraphEvent {
    override def getLiteral: Literal = literal
    override def toString: String = {
      s"Decision(${Literal.toString(literal)}, ${previousDecision.map(Literal.toString)})"
    }
  }

  /**
    * Literal chosen by unit propagation or pure literal rule.
    * @param literal – The literal that was chosen.
    * @param predecessorLiterals – The literals that point to this literal in the implication graph.
    */
  case class Consequence(literal: Literal,
                         predecessorLiterals: mutable.ArrayBuffer[Literal]) extends GraphEvent {
    override def getLiteral: Literal = literal
    override def toString: String = {
      s"Consequence(${Literal.toString(literal)}, ${predecessorLiterals.map(Literal.toString)})"
    }
  }

  // the stack of decisions / consequences at the current point in the search
  private val eventLog: ArrayBuffer[Event] = mutable.ArrayBuffer[Event]()

  // In this implementation, it's convenient to index the arrays below by variables rather than literals.
  // Since we assume that no two literals for the same variable ever need to be added to the same graph, we
  // can use the variable contained in the literal to uniquely identify the node in question.

  // maps variables (representing literals) to the level at which a decision for this literal was taken
  private val _decisionLevel = new Array[Variable](literalCount+1)
  private var _currentDecisionLevel = 0
  private var _lastDecision: Option[Literal] = None

  // represents the graph edges (only the "consequence" edges; the stack of decisions is represented above)
  private val predecessors = new Array[mutable.ArrayBuffer[Variable]](literalCount+1)
  private val successors = new Array[mutable.ArrayBuffer[Variable]](literalCount+1)

  // records any current event (cause for adding the literal to the graph) for a particular literal
  private val variableEvents = new Array[Option[Event]](literalCount+1)

  clear()

  private def debug(msg: => String): Unit = {
    if (verbose) {
     // println("  " * _currentDecisionLevel + msg)
    }
  }

  private def setDecisionLevel(literal: Literal): Unit = {
    _decisionLevel(Literal.toVariable(literal)) = _currentDecisionLevel
  }

  private def clearDecisionLevel(literal: Literal): Unit = {
    _decisionLevel(Literal.toVariable(literal)) = -1
  }

  /**
    * Log the literal that was chosen by the decision rule.
    *
    * Note: Adding the same variable more than once to the graph most likely means
    * that you have a bug (choosing the same literal twice is pointless, and
    * choosing ¬l when you have already chosen l means that you have a conflict,
    * so there is no point in adding ¬l to the implication graph). Therefore, the
    * implementation assumes that you do not try to add the same variable more
    * than once.
    */
  def logDecision(literal: Literal): Unit = {
    debug(s"logDecision: literal=${Literal.toString(literal)}")
    if (_currentDecisionLevel == 0) {
      // We need to distinguish first decision literal from all literals that can
      // be removed without making any decisions.
      _currentDecisionLevel = 1
    }
    setDecisionLevel(literal)
    _currentDecisionLevel += 1
    eventLog.append(Decision(literal, _lastDecision))
    val variable = Literal.toVariable(literal)
    assert(variableEvents(variable).isEmpty)
    variableEvents(variable) = Some(eventLog.last)
    _lastDecision = Some(literal)
  }

  /**
    * Log the literal that was chosen by the unit or pure literal rule.
    *
    * Note: Adding the same variable more than once to the graph most likely means
    * that you have a bug (choosing the same literal twice shouldn't happen, and
    * choosing ¬l when you have already chosen l means that you have a conflict,
    * so there is no need to add ¬l to the implication graph). Therefore, the
    * implementation asserts that you do not try to add the same variable more
    * than once.
    *
    * @param predecessorLiterals – The literals that point to this literal in the implication graph.
    */
  def logConsequence(literal: Literal, predecessorLiterals: mutable.ArrayBuffer[Literal]): Unit = {
    debug(
      s"logConsequence:" +
      s" literal=${Literal.toString(literal)} (${Literal.toVariable(literal)})")
    setDecisionLevel(literal)
    eventLog.append(Consequence(literal, predecessorLiterals))
    var i = 0
    val variable = Literal.toVariable(literal)
    while (i < predecessorLiterals.length) {
      val pred = predecessorLiterals(i)
      val predVar = Literal.toVariable(pred)
      predecessors(variable).append(pred)
      successors(predVar).append(literal)
      i += 1
    }
    assert(variableEvents(variable).isEmpty,
      s"${variableEvents(variable).get.toString} is not None for ${Literal.toString(literal)}")
    variableEvents(variable) = Some(eventLog.last)
  }

  /**
    * Log under the last event that the clause was disabled because one of its
    * literals became true.
    * @param index – The index of the disabled clause.
    */
  def logDisableClause(index: Int): Unit = {
    require(eventLog.nonEmpty)
    eventLog.last.registerDisabledClause(index)
  }

  /**
    * Log under the last event that the literal was disabled because it became false.
    * @param clauseIndex – The index of the clause to which the literal belongs.
    * @param literalIndex – The index of the literal inside the clause.
    */
  def logDisableLiteral(clauseIndex: Int, literalIndex: Int): Unit = {
    require(eventLog.nonEmpty)
    eventLog.last.registerDisabledLiteral(clauseIndex, literalIndex)
  }

  /**
    * Get the last decision literal.
    */
  def lastDecision: Literal = {
    _lastDecision.get
  }

  /**
    * Get the last decision literal.
    */
  def lastDecisionOption: Option[Literal] = {
    _lastDecision
  }

  /**
    * Are there any events logged?
    */
  def nonEmpty: Boolean = {
    eventLog.size > 1
  }

  /**
    * Get the last event.
    */
  def lastEvent(): Option[Event] = {
    eventLog.last match {
      case Start() => None
      case _ => Some(eventLog.last)
    }
  }

  /**
    * Get the event that was about this literal.
    */
  def getEvent(literal: Literal): Event = {
    val variable = Literal.toVariable(literal)
    variableEvents(variable).get
  }

  /**
    * Pop the last event and undo its effects on the graph.
    */
  def popEvent(): Unit = {
    require(nonEmpty)
    eventLog.last match {
      case Start() =>
        assert(false, "Bug!")
      case event@Decision(literal, previousDecision) =>
        debug(s"popEvent $event")
        _currentDecisionLevel -= 1
        clearDecisionLevel(literal)
        _lastDecision = previousDecision
        val variable = Literal.toVariable(literal)
        assert(variableEvents(variable).isDefined)
        variableEvents(variable) = None
      case event@Consequence(literal, predecessorLiterals) =>
        debug(s"popEvent $event")
        clearDecisionLevel(literal)
        val variable = Literal.toVariable(literal)
        var i = predecessorLiterals.length
        while (i > 0) {
          i -= 1
          val pred = predecessorLiterals(i)
          val predVar = Literal.toVariable(pred)
          assert(predecessors(variable).last == pred, "Bug!")
          predecessors(variable).remove(predecessors(variable).length-1)
          assert(successors(predVar).last == literal, "Bug!")
          successors(predVar).remove(successors(predVar).length-1)
        }
        assert(variableEvents(variable).isDefined)
        variableEvents(variable) = None
    }
    eventLog.remove(eventLog.length-1)
  }

  /**
    * Get literals that point to the given literal in the implication graph.
    */
  def getPredecessors(literal: Literal): mutable.ArrayBuffer[Literal] = {
    val variable = Literal.toVariable(literal)
    predecessors(variable)
  }

  /**
    * Get literals that are pointed at by the given literal in the implication graph.
    */
  def getSuccessors(literal: Literal): mutable.ArrayBuffer[Literal] = {
    val variable = Literal.toVariable(literal)
    successors(variable)
  }

  /**
    * Get the decision level of the literal.
    *
    * If the literal was logged as a consequence before any decision, then its level is 0.
    * If the literal was logged as a decision, then its level is the decision depth (starting from 1).
    * If the literal was logged as a consequence, then its level is the decision depth + 1.
    */
  def decisionLevel(literal: Literal): Int = {
    val variable = Literal.toVariable(literal)
    _decisionLevel(variable)
  }

  /**
    * Return the current decision level.
    */
  def currentDecisionLevel: Int = {
    _currentDecisionLevel
  }

  /**
    * Clear the implication graph.
    */
  def clear(): Unit = {
    eventLog.clear()
    eventLog.append(Start())
    _currentDecisionLevel = 0
    _lastDecision = None
    var i = 0
    while (i < literalCount+1) {
      clearDecisionLevel(i)
      predecessors(i) = mutable.ArrayBuffer()
      successors(i) = mutable.ArrayBuffer()
      variableEvents(i) = None
      i += 1
    }
  }

  /**
    * Perform a very basic check that the graph is not corrupted.
    */
  def checkConsistency(): Unit = {
    // Check the event log.
    assert(eventLog(0) == Start())
    val loggedVariables = mutable.HashSet[Variable]()
    var i = 1
    while (i < eventLog.length) {
      val event = eventLog(i)
      val literal = event.getLiteral
      val variable = Literal.toVariable(literal)
      assert(
        !loggedVariables.contains(variable),
        s"The same variable is logged more than once: ${Literal.toString(variable)}")
      loggedVariables.add(variable)
      i += 1
    }
  }

  /**
    * Create a dot file with the current state of the implication graph.
    *
    * You can render it with graphviz by using a command: dot -Tps graph.dot -Ograph.ps
    *
    * @param path – The path to the file to which this graph should be written to.
    * @param highlight – Literals that should be highlighted.
    */
  def writeAsDot(path: String, highlight: Seq[Literal]): Unit = {
    val printer = new PrintWriter(new File(path))
    printer.println("digraph g {")
    def printLiteral(literal: Literal, style: Map[String,Seq[String]]): Unit = {
      val newStyle = if (highlight.contains(literal)) {
        style.updated("fillcolor", Seq("green"))
      } else {
        style
      }
      val nodeId = Literal.toString(Literal.toVariable(literal))
      val label = Literal.toString(literal)
      val styleString = newStyle.map(k => s"""${k._1}="${k._2.mkString(",")}" """).mkString(" ")
      printer.println(s"""  "$nodeId" [label="$label" $styleString]""")
    }
    def printEdge(source: Literal, target: Literal, style: Map[String,Seq[String]]): Unit = {
      val sourceNodeId = Literal.toString(Literal.toVariable(source))
      val targetNodeId = Literal.toString(Literal.toVariable(target))
      val styleString = style.map(k => s"""${k._1}="${k._2.mkString(",")}" """).mkString(" ")
      printer.println(s"""  "$sourceNodeId" -> "$targetNodeId" [$styleString]""")
    }
    def printDecision(literal: Literal): Unit = {
      printLiteral(literal, Map(
        "shape"->Seq("circle"),
        "style"->Seq("filled", "dashed"),
        "fillcolor"->Seq("white"),
        "color"->Seq("red"),
        "fontcolor"->Seq("red")
      ))
    }
    var i = 0
    while (i < eventLog.length) {
      eventLog(i) match {
        case Start() =>
        case Decision(literal, None) =>
          printDecision(literal)
        case Decision(literal, Some(previous)) =>
          printDecision(literal)
          printEdge(previous, literal, Map(
            "style"->Seq("dashed"),
            "color"->Seq("red")
          ))
        case Consequence(literal, _) =>
          printLiteral(literal, Map(
            "shape"->Seq("circle"),
            "style"->Seq("filled", "solid"),
            "fillcolor"->Seq("white"),
            "color"->Seq("blue"),
            "fontcolor"->Seq("blue")
          ))
          val preds = predecessors(Literal.toVariable(literal))
          var j = 0
          while (j < preds.length) {
            printEdge(preds(j), literal, Map(
              "style"->Seq("solid"),
              "color"->Seq("blue")
            ))
            j += 1
          }
      }
      i += 1
    }
    printer.println("}")
    printer.close()
  }

}
