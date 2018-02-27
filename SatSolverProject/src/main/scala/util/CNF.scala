package util

import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier, Term}
import smtlib.theories.Core._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * A formula in CNF form.
  */
final class Formula {

  /**
    * We use positive integers as variable names because this is much faster than using strings.
    */
  type Variable = Int

  /**
    * A singleton object that defines functions for working with variables.
    */
  object Variable {

    /**
      * l := v
      */
    def toLiteral(variable: Variable): Literal = {
      variable
    }

    /**
      * l := ¬v
      */
    def toNegatedLiteral(variable: Variable): Literal = {
      (1 << 31) | variable
    }

  }

  /**
    * Literal is just a variable with some bits used to indicate its status:
    * + is the literal negated or not;
    * + is the literal disabled (removed from the clause) or not.
    */
  type Literal = Int

  /**
    * A singleton object that defines functions for working with literals.
    */
  object Literal {

    /**
      * Check if the literal is negated.
      */
    def isNegated(literal: Literal): Boolean = {
      (literal & (1 << 31)) != 0
    }

    /**
      * Negate literal.
      */
    def neg(literal: Literal): Literal = {
      literal ^ (1 << 31)
    }

    /**
      * Check if literal is enabled.
      */
    def isEnabled(literal: Literal): Boolean = {
      (literal & (1 << 30)) == 0
    }

    /**
      * Convert the enabled literal to the disabled literal.
      */
    def disable(literal: Literal): Literal = {
      assert(isEnabled(literal))
      val result = literal | (1 << 30)
      assert(!isEnabled(result))
      result
    }

    /**
      * Convert the disabled literal to the enabled literal.
      */
    def enable(literal: Literal): Literal = {
      assert(!isEnabled(literal))
      val result = literal ^ (1 << 30)
      assert(isEnabled(result))
      result
    }

    /**
      * Convert the literal to the variable.
      */
    def toVariable(literal: Literal): Variable = {
      literal & ((1 << 20) - 1)
    }

    /**
      * Check if two literals correspond to the same variable.
      */
    def isSameVariable(first: Literal, second: Literal): Boolean = {
      toVariable(first) == toVariable(second)
    }

    /**
      * Convert literal to an user readable string.
      */
    def toString(literal: Option[Literal]): String = {
      literal match {
        case Some(lit) => s"Some(${toString(lit)})"
        case None => "None"
      }
    }

    /**
      * Convert literal to an user readable string.
      * If the literal is a negate variable, then ¬ is prepended before the variable name.
      * If the literal is disabled, then ! is appended after the variable name.
      */
    def toString(literal: Literal): String = {
      val name = variableNames(toVariable(literal))
      s"${if (isNegated(literal)) "¬" else ""}$name${if (!isEnabled(literal)) "!" else ""}"
    }

    /**
      * Convert to a SMTLib Term.
      */
    def toTerm(literal: Literal): Term = {
      val name = variableNames(Literal.toVariable(literal))
      if (Literal.isNegated(literal)) {
        Not(QualifiedIdentifier(SimpleIdentifier(SSymbol(name))))
      } else {
        QualifiedIdentifier(SimpleIdentifier(SSymbol(name)))
      }
    }

  }

  /**
    * A clause.
    */
  final class Clause {

    /**
      * Is this clause enabled?
      */
    var enabled = true

    /**
      * Literals of this clause.
      */
    val literals: ArrayBuffer[Literal] = ArrayBuffer[Literal]()

    /**
      * Add the literal to the clause.
      * @param literal The literal to add.
      * @return True if successfully added. False if the literal was already in the clause.
      */
    def add(literal: Literal): Boolean = {
      if (!literals.contains(literal)) {
        literals.append(literal)
        true
      } else {
        false
      }
    }

    def map[T](function: Literal => T): Seq[T] = {
      literals.map(function)
    }

    def nonEmpty: Boolean = {
      literals.nonEmpty
    }

    def isSingleton: Boolean = {
      literals.size == 1
    }

    def foreachEnabled(function: Literal => Unit): Unit = {
      literals.foreach((literal) => {
        if (Literal.isEnabled(literal)) {
          function(literal)
        }
      })
    }

    def disableLiteral(index: Int): Unit = {
      literals(index) = Literal.disable(literals(index))
    }

    def enableLiteral(index: Int): Unit = {
      literals(index) = Literal.enable(literals(index))
    }

    /**
      * Count how many enabled literals this clause contains.
      */
    def enabledLiteralsCount: Int = {
      var i = 0
      var count = 0
      while (i < literals.length) {
        if (Literal.isEnabled(literals(i))) {
          count += 1
        }
        i += 1
      }
      count
    }

    override def toString: String = {
      val stringLiterals = literals.map((literal) => Literal.toString(literal))
      s"(${stringLiterals.mkString(",")})${if (!enabled) "!" else ""}"
    }

    /**
      * Convert to a SMT Lib term.
      */
    def toTerm: Term = {
      require(nonEmpty)
      if (isSingleton) {
        Literal.toTerm(literals.head)
      } else {
        Or(literals.map(Literal.toTerm).toSeq)
      }
    }

  }

  /**
    * A model for this formula. This class is nested just to simplify getting back proper
    * names for literals.
    */
  final class Model {

    /**
      * Literals that are true in the model.
      */
    val literals: mutable.HashSet[Literal] = mutable.HashSet[Literal]()

    /**
      * Add the literal to the model.
      */
    def addLiteral(literal: Literal): Unit = {
      assert(
        !literals.contains(Literal.neg(literal)),
        s"Bug: Trying to add a literal ${Literal.toString(literal)} " +
          s"while model already contains its negation ${Literal.toString(Literal.neg(literal))}. " +
          s"Model: ${literals.map(Literal.toString).mkString(", ")}.")
      if (!literals.contains(literal)) {
        literals.add(literal)
      }
    }

    def isEmpty: Boolean = {
      literals.isEmpty
    }

    /**
      * a String representation (according to the SMT-LIB standard)
      */
    override def toString: String = {
      val builder = new StringBuilder
      builder.append("sat\n(model\n")
      literals.foreach((literal) => {
        val id = variableNames(Literal.toVariable(literal))
        builder.append(s"(define-fun $id) Bool ${!Literal.isNegated(literal)})")
      })
      builder.append(")")
      builder.toString()
    }

    /**
      * Convert to the map representation.
      */
    def toMap: Map[String, Boolean] = {
      literals.map((literal) => {
        val name = variableNames(Literal.toVariable(literal))
        (name, !Literal.isNegated(literal))
      }).toMap
    }
  }

  /**
    * Clauses of this formula.
    */
  val clauses: ArrayBuffer[Clause] = mutable.ArrayBuffer[Clause]()

  private val variableIds = mutable.HashMap[String, Variable]()
  private val variableNames = mutable.HashMap[Variable, String]()
  private var lastId = 1
  private var containsEmptyClause = false

  /**
    * Additional constructor that converts the passed in formula to CNF form.
    */
  def this(term: Term) {
    this()
    val originalVariables = PropositionalLogic.propositionalVariables(term)
    originalVariables.foreach(name => {
      val variable = getFreshVariable
      variableIds(name) = variable
      variableNames(variable) = name
    })

    // TODO: Finish the implementation.
    ???
  }

  /**
   * Simplify the formula.
   */
  private def simplify(formula: Term): Term = ???

  private def getFreshVariable: Variable = {
    val oldLastId = lastId
    lastId += 1
    oldLastId
  }

  private var lastVarId = 1
  /**
    * Get a fresh variable that is not yet used in the formula.
    */
  private def getFreshSMTVar: Term = {
    var candidateName = s"v$lastVarId"
    while (variableIds.contains(candidateName)) {
      lastVarId += 1
      candidateName = s"v$lastVarId"
    }
    val variable = QualifiedIdentifier(SimpleIdentifier(SSymbol(candidateName)))
    lastVarId += 1
    variable
  }

  /**
    * Get the variable that has the given name.
    */
  def getVariableFromName(name: String): Variable = {
    variableIds(name)
  }

  /**
    * Get the number of literals used in this formula.
    * Invariant: literal ids are from range [1, literalCount]
    */
  def literalCount: Literal = {
    lastId - 1
  }

  /**
    * Add a clause to the formula.
    * @param literals – Literals of the clause.
    */
  def addClause(literals: Seq[Term]): Unit = {
    require(literals.nonEmpty)
    val clause = new Clause
    literals.map(simplify).foreach {
      case v@QualifiedIdentifier(SimpleIdentifier(id), _) =>
        if (!variableIds.contains(id.name)) {
          val variable = getFreshVariable
          variableIds(id.name) = variable
          variableNames(variable) = id.name
        }
        clause.add(Variable.toLiteral(variableIds(id.name)))
      case v@Not(QualifiedIdentifier(SimpleIdentifier(id), _)) =>
        if (!variableIds.contains(id.name)) {
          val variable = getFreshVariable
          variableIds(id.name) = variable
          variableNames(variable) = id.name
        }
        clause.add(Variable.toNegatedLiteral(variableIds(id.name)))
    }
    clauses.append(clause)
  }

  /**
    * Prints formula to stdout.
    * ¬ – before literal marks that it is negated
    * ! – after literal marks that it is disabled
    * ! – after clause marks that it is disabled
    */
  def printDebugToStdout(): Unit = {
    if (containsEmptyClause) {
      println("[()]")
    } else {
      println("[")
      clauses.map(_.toString).foreach(println)
      println("]")
    }
  }

  override def toString: String = {
    if (containsEmptyClause) {
      "[()]"
    } else {
      s"[${clauses.map(_.toString).mkString(",")}]"
    }
  }

  /**
    * Convert to a SMTLib Term.
    */
  def toTerm: Term = {
    if (containsEmptyClause) {
      return False()
    }
    if (clauses.isEmpty) {
      return True()
    }
    if (clauses.length < 2) {
      clauses.head.toTerm
    }
    else {
      And(clauses.map(_.toTerm))
    }
  }

  /**
    * True if this formula contains no clauses.
    */
  def isEmpty: Boolean = {
    clauses.isEmpty
  }

  /**
    * True if this formula contains an empty clause.
    */
  def hasEmptyClause: Boolean = {
    containsEmptyClause
  }

  /**
    * Iterate over all enabled clauses.
    */
  def foreachEnabled(function: Clause => Unit): Unit = {
    clauses.foreach((clause) => {
      if (clause.enabled) {
        function(clause)
      }
    })
  }

}
