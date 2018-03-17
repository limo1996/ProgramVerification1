package util

import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier, Term}
import smtlib.theories.Core._
import smtlib.theories.Constructors._
import smtlib.theories.Operations.OperationN

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer

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

    // converts formula to CNF and stores it in this object
    simplify(term)
  }

  /*
   * The functions step? implement different steps of the 'Conversion to CNF'
   * algorithm presented in lecture slide 10.
   */

  /*
   * Original step 1
   * Rewrite implications and equivalences and recursively handle them.
   * For all the other terms recursively handle to their children.
   */
  private def step1(formula: Term) : Term = formula match {
    case True() | False() => formula
    case QualifiedIdentifier(SimpleIdentifier(_), _) => formula
    case Not(f) => Not(step1(f))
    case Or(disjuncts@_*) => Or(disjuncts.map(c => step1(c)))
    case And(conjuncts@_*) => And(conjuncts.map(c => step1(c)))
    case Implies(f, g) => Or(Not(step1(f)), step1(g))
    case Equals(f, g) => And(Or(Not(step1(f)), step1(g)), Or(step1(f), Not(step1(g))))
    case _ => throw new Exception("step1")  // this shouldn't happen
  }

  /*
   * Original step 2 & step 3 & step4
   * step 2: Push negations inwards.
   * step 3: Eliminate double negations when found.
   * step 4: Eliminate True from conjunctions and remove clauses containing True.
   *         Eliminate False from clauses and remove conjunctions containing False.
   *
   * When there is not negation to match (e.g. AND/OR) try to descend to terms children.
   * Step 4 is done with the help of the 'or' and 'and' constructors which also flatten
   * formulas with nested 'or' and 'and' terms respectively. e.g. or(a, or(b,c)) => or(a, b, c)
   */
  private def step2(formula: Term) : Term = formula match {
    case True() | False() => formula
    case Not(True()) => False()
    case Not(False()) => True()
    case QualifiedIdentifier(SimpleIdentifier(_), _) => formula
    case Not(QualifiedIdentifier(SimpleIdentifier(_), _)) => formula
    case Or(disjuncts@_*) => or(disjuncts.map(c => step2(c)))
    case And(conjuncts@_*) => and(conjuncts.map(c => step2(c)))
    case Not(Or(disjuncts@_*)) => and(disjuncts.map(c => step2(Not(c))))
    case Not(And(conjuncts@_*)) => or(conjuncts.map(c => step2(Not(c))))
    case Not(Not(f)) => step2(f)
    case _ => throw new Exception("step2")  // this shouldn't happen
  }

  /*
   * List that after call of tseitin will contain all equivalences that tseitin produses.
   * We will still need to simplify them thought.
   */
  private val t_list = new ListBuffer[Term]()

  /*
   * Provided with a sequence of terms, return one term by replacing pairs of terms with newly introduced variables.
   * The terms are expected to be literals that belong to a disjunction or conjunction (specified by the op parameter).
   * Equivalences (new var is equivalent to the (dis/con)junction of two literals) generated during this process are
   * stored in t_list.
   */
  private def tseitinReplace(terms: Seq[Term], op: OperationN): Term = {
    if (terms.lengthCompare(1) == 0) terms.head     // if size is one return literal
    else {                                          // if size is greater than 1
      val fresh_var : Term = getFreshSMTVar         // introduce new var
      val (first_two, rest) = terms.splitAt(2)      // the list of literals is split in the first two and the rest
      t_list += Equals(fresh_var, op(first_two))    // new var represents the (dis/con)junction of the first two literals
      tseitinReplace(fresh_var +: rest, op)         // continue with the new formula of size = old(size) - 1
    }
  }

  /*
   * Applies Tseitin transformation => https://en.wikipedia.org/wiki/Tseytin_transformation
   * We assume that formula contains just conjuctions, disjunctions and negations.
   * All equivalences that are created during process are stored in t_list.
   */
  private def tseitin(formula: Term): Term = {
    //println("Tseitin: " + formula)
    formula match {
      case And(conjuncts@_*) =>                                       // Conjunction
        if(conjuncts.forall(c => PropositionalLogic.isLiteral(c))) tseitinReplace(conjuncts, And) // if all are pure literals apply convertAnd function on them
        else tseitin(And(conjuncts.map(c => tseitin(c))))             // else we need to apply tseitin on children, conjoin resulting variables and call tseitin on them again
      case Or(disjuncts@_*) =>                                        // Disjunction
        if(disjuncts.forall(c => PropositionalLogic.isLiteral(c))) tseitinReplace(disjuncts, Or) // if all are pure literals apply convertOr function on them
        else tseitin(Or(disjuncts.map(c => tseitin(c))))              // else we need to apply tseitin on children, disjoin resulting variables and call tseitin on them again.
      case QualifiedIdentifier(SimpleIdentifier(_), _) | Not(QualifiedIdentifier(SimpleIdentifier(_), _)) =>
        t_list :+ formula                                             // if whole formula is just one literal (could be negated) than add it to t_list and return
        formula
      case _ => throw new Exception("tseitin: unexpected input Term: " + formula)
    }
  }

  /*
   * Simplifies equality produced by tseitin into conjuction (returns elements of conjuction)
   */
  private def simplifyEquality(formula: Term): Seq[Term] = {
    formula match {
      case Equals(a, g) =>
        g match {
          case And(b, c) => Seq(Or(Not(a), b), Or(Not(a), c), Or(a, Not(b), Not(c))).map(step2)
          case Or(b, c) => Seq(Or(Not(a), b, c), Or(a, Not(b)), Or(a, Not(c))).map(step2)
          case _ => throw new Exception("simplifyEquality: unexpected input Term " + formula)
        }
      case QualifiedIdentifier(SimpleIdentifier(_), _) => Seq(formula)
      case _ => throw new Exception("simplifyEquality: unexpected input Term " + formula)
    }
  }

  /*
   * Simplifies formulas produced by tsetin and returns them as conjuction (CNF)
   */
  private def simplifyTseitin(): Unit = {
    val cnf = ListBuffer[Term]()
    for (c <- t_list) {
      cnf ++= simplifyEquality(c)
    }
    if (cnf.lengthCompare(0) == 0) containsEmptyClause = true
    else if (cnf.lengthCompare(1) == 0) addClause(cnf)
    else {
      for (c <- cnf) {
        c match {
          case Or(disjuncts@_*) => addClause(disjuncts)
          case QualifiedIdentifier(SimpleIdentifier(_), _) => addClause(List(c))
          case _ => throw new Exception("simplify")
        }
      }
    }
  }

  /**
   * Simplify the formula.
   */
  private def simplify(formula: Term): Unit = {

    val simplified1 = step2(step1(formula))
    if(PropositionalLogic.isCNF(simplified1)){
      simplified1 match {
        case And(conjuncts@_*) => {
          for (c <- conjuncts) {
            c match {
              case Or(disjuncts@_*) => addClause(disjuncts)
              case QualifiedIdentifier(SimpleIdentifier(_), _) | Not(QualifiedIdentifier(SimpleIdentifier(_), _)) | True() | False() => addClause(List(c))
            }
          }
        }
        case Or(disjuncts@_*) => addClause(disjuncts)
        case QualifiedIdentifier(SimpleIdentifier(_), _) | Not(QualifiedIdentifier(SimpleIdentifier(_), _)) | True() | False() => addClause(List(simplified1))
      }
    } else {
      val simplified2 = tseitin(simplified1)
      //println("simplified 2 " + simplified2)
      t_list += simplified2
      simplifyTseitin()
    }
  }

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
    var is_true = false
    literals.foreach {
      case v@QualifiedIdentifier(SimpleIdentifier(id), _) =>
        if (!variableIds.contains(id.name)) {
          val variable = getFreshVariable
          variableIds(id.name) = variable
          variableNames(variable) = id.name
        }
        val vv = Variable.toLiteral(variableIds(id.name))
        if (!clause.literals.contains(vv))
          clause.add(vv)
        if (clause.literals.contains(Literal.neg(vv)))
          is_true = true
      case v@Not(QualifiedIdentifier(SimpleIdentifier(id), _)) =>
        if (!variableIds.contains(id.name)) {
          val variable = getFreshVariable
          variableIds(id.name) = variable
          variableNames(variable) = id.name
        }
        val vv = Variable.toNegatedLiteral(variableIds(id.name))
        if (!clause.literals.contains(vv))
          clause.add(vv)
        if (clause.literals.contains(Literal.neg(vv)))
          is_true = true

    }
    if (!is_true) clauses.append(clause)
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
