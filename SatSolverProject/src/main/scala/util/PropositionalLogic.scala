package util

import smtlib.parser.Terms.{QualifiedIdentifier, SimpleIdentifier, Term}
import smtlib.theories.Core._

object PropositionalLogic {
  // checks that the given Term is a propositional logic formula, according to the lecture slides syntax
  def isPropositional(formula : Term) : Boolean = {
    formula match {
      case True() | False() => true // syntax for defining multiple cases at once
      case QualifiedIdentifier(SimpleIdentifier(id), _) => true // propositional variable with SSymbol identifier "id"
      case Not(f) => isPropositional(f)
      case Or(disjuncts@_*) => // The Or and And constructors take variable-length argument sequences; this is the generalised pattern-matching sequence for matching an Or with "disjuncts" as the sequence of disjunct terms (which is a Scala Seq[Term] value)
        disjuncts.forall(d => isPropositional(d)) // "forall" is a built-in method on the Scala Seq[T] type; see http://www.scala-lang.org/api/2.12.0/scala/collection/Seq.html
      case And(conjuncts@_*) => conjuncts.forall(c => isPropositional(c))
      case Implies(f,g) => isPropositional(f) && isPropositional(g)
      case Equals(f,g) => isPropositional(f) && isPropositional(g) // "if and only if" is represented using Equals on the subformulas
      case _ => false
    }
  }

  // get all propositional variables occurring in the propositional formula, and return a set of them
  def propositionalVariables(formula : Term) : Set[String] = formula match {
    case True() | False() => Set() // syntax for defining multiple cases at once
    case QualifiedIdentifier(SimpleIdentifier(id), _) => Set(id.name) // propositional variable with SSymbol identifier "id"
    case Not(f) => propositionalVariables(f)
    case Or(disjuncts@_*) => // The Or and And constructors take variable-length argument sequences; this is the generalised pattern-matching sequence for matching an Or with "disjuncts" as the sequence of disjunct terms (which is a Scala Seq[Term] value)
      disjuncts.foldLeft[Set[String]](Set())((set,d) => set union propositionalVariables(d)) // See foldLeft in http://www.scala-lang.org/api/2.12.0/scala/collection/Seq.html
    case And(conjuncts@_*) => conjuncts.foldLeft[Set[String]](Set())((set,c) => set union propositionalVariables(c))
    case Implies(f,g) => propositionalVariables(f) union propositionalVariables(g)
    case Equals(f,g) => propositionalVariables(f) union propositionalVariables(g)
  }

  // is the given propositional formula a literal?
  def isLiteral(formula : Term) : Boolean = formula match { // braces are optional for the top-level of a method body definition
    case QualifiedIdentifier(SimpleIdentifier(_), _) => true
    case Not(QualifiedIdentifier(SimpleIdentifier(_), _)) => true
    case _ => false
  }

  // is the given formula a clause?
  def isClause(formula : Term) : Boolean = formula match {
    case False() => true // represents empty clause / empty disjunction
    case _ if isLiteral(formula) => true // adding "if b" to a case condition causes it only to match if the attached condition holds
    case Or(disjuncts@_*) => disjuncts.forall(d => isLiteral(d))
    case _ => false
  }

  // is the given formula in CNF form?
  def isCNF(formula : Term) : Boolean = formula match {
    case True() => true // empty conjunction
    case _ if isClause(formula) => true // a single clause is OK
    case And(conjuncts@_*) => conjuncts.forall(c => isClause(c))
    case _ => false
  }

  /**
    * Evaluate the formula in the model.
    */
  def evaluate(formula: Term, model: Map[String, Boolean]): Boolean = {
    formula match {
      case True() => true
      case False() => false
      case QualifiedIdentifier(SimpleIdentifier(id), _) => model(id.name)
      case Not(f) => !evaluate(f, model)
      case Or(disjuncts@_*) => disjuncts.exists(d => evaluate(d, model))
      case And(conjuncts@_*) => conjuncts.forall(c => evaluate(c, model))
      case Implies(f, g) => !evaluate(f, model) || evaluate(g, model)
      case Equals(f, g) => evaluate(f, model) == evaluate(g, model)
      case _ => ???
    }
  }

}
