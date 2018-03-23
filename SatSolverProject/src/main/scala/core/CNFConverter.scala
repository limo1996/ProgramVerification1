package core

import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier, Term}
import smtlib.theories.Core._
import smtlib.theories.Constructors._
import smtlib.theories.Operations.OperationN

object CNFConverter {

  // Converts given propositional formula into CNF formula.
  def convert(formula: Term, useTseitin: Boolean): Term = {
    var f = step1(formula)
    f = step23(f)
    f = step4(f)

    // in case of tseitin apply just first 4 steps
    if(useTseitin)
      return f

    f = step5(f)
    step6(f)
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
  def step1(formula: Term) : Term = formula match {
    case True() | False() => formula
    case QualifiedIdentifier(SimpleIdentifier(_), _) => formula
    case Not(f) => Not(step1(f))
    case Or(disjuncts@_*) => handleDisjunctsSeq(disjuncts.map(c => step1(c)))
    case And(conjuncts@_*) => handleConjunctsSeq(conjuncts.map(c => step1(c)))
    case Implies(f, g) => Or(Not(step1(f)), step1(g))
    case Equals(f, g) =>
      val _f = step1(f)
      val _g = step1(g)
      And(Or(Not(_f), _g), Or(_f, Not(_g)))
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
  def step23(formula: Term) : Term = formula match {
    case True() | False() => formula
    case Not(True()) => False()
    case Not(False()) => True()
    case QualifiedIdentifier(SimpleIdentifier(_), _) => formula
    case Not(QualifiedIdentifier(SimpleIdentifier(_), _)) => formula
    case Or(disjuncts@_*) => handleDisjunctsSeq(disjuncts.map(c => step23(c)))
    case And(conjuncts@_*) => handleConjunctsSeq(conjuncts.map(c => step23(c)))
    case Not(Or(disjuncts@_*)) => handleConjunctsSeq(disjuncts.map(c => step23(Not(c))))
    case Not(And(conjuncts@_*)) => handleDisjunctsSeq(conjuncts.map(c => step23(Not(c))))
    case Not(Not(f)) => step23(f)
    case _ => throw new Exception("step23")  // this shouldn't happen
  }

  /**
    * Applies step 4 from the lecture slides.
    * I.e removes true and false clauses which are in CNF case irrelevant.
    * Rules:  if there is true in disjunction then we can remove it.
    *         if there is false in disjunction we can remove it
    *         if there is true in conjuction we can remove it
    *         if there is false in conjunction we can replace clause with false
    */
  def step4(formula: Term): Term = {
    formula match {
      case Or(disjuncts@_*) => {
        val processed = disjuncts.map(c => step4(c)).filter({
            case False() => false
            case _ => true
          })
        val containsTrue = processed.collect({ case True() => True() }).size > 0
        if (containsTrue) {
          True()
        } else {
          handleDisjunctsSeq(processed)
        }
      }
      case Not(f) => Not(step4(f))
      case And(conjuncts@_*) =>
        val processedConjuncts = conjuncts.map(c => step4(c)).filter({
            case True() => false
            case _ => true
          })
        val containsFalse = processedConjuncts.collect({ case False() => False() }).size > 0
        if (containsFalse) {
          False()
        } else {
          handleConjunctsSeq(processedConjuncts)
        }
      case _ => formula
    }
  }

  /**
    * Applies step 5 from the lecture slides.
    * Distributes Conjunctions over disjunctions
    */
  def step5(formula: Term): Term = {
    formula match {
      case Not(f) => Not(step5(f))
      case Or(disjuncts@_*) =>
        // recurse first
        val processedDisjuncts = disjuncts.map(d => step5(d))
        // collect the disjuncts that are conjuncts
        val disjunctConjuncts = processedDisjuncts.collect({
          case And(conjuncts2@_*) => And(conjuncts2)
        }).toList
        val conjuncts = processedDisjuncts.collect({
          case And(conjuncts2@_*) => conjuncts2.toList
        }).toList
        // collect disjuncts that are not conjuncts
        val pureDisjuncts = processedDisjuncts.filter(p => !disjunctConjuncts.contains(p)).toList
        if (conjuncts.nonEmpty) {
          val conjunctsCombination = getCombinations(conjuncts)
          flatten(handleConjunctsSeq(conjunctsCombination.map(c => handleDisjunctsSeq(pureDisjuncts ++ c))))
        } else {
          flatten(handleDisjunctsSeq(processedDisjuncts))
        }
      case And(conjuncts@_*) => flatten(handleConjunctsSeq(conjuncts.map(c => step5(c))))
      case _ => formula
    }
  }

  /**
    * Method that flattens nested Ors and Ands
    */
  def flatten(formula: Term): Term = {
    formula match {
      case And(conjuncts@_*) =>
        // recurse first:
        val processedConjuncts = conjuncts.map(c => flatten(c))
        val unwrappedConjuncts = processedConjuncts.flatMap {
          case And(innerConjuncts@_*) => innerConjuncts
          case c => List(c)
        }
        handleConjunctsSeq(unwrappedConjuncts)
      case Or(disjuncts@_*) =>
        // recurse first:
        val processedDisjuncts = disjuncts.map(c => flatten(c))
        val unwrappedDisjuncts = processedDisjuncts.flatMap {
          case Or(innerDisjuncts@_*) => innerDisjuncts
          case c => List(c)
        }
        handleDisjunctsSeq(unwrappedDisjuncts)
      case _ => formula
    }
  }

  /**
    * Applies step 6 from the lecture slides. I.e. removes duplicate clauses and literals in clause.
    */
  def step6(formula: Term): Term = {
    formula match {
      case And(conjuncts@_*) =>
        handleConjunctsSeq(conjuncts.distinct.map(c => step6(c)))
      case Or(disjuncts@_*) =>
        handleDisjunctsSeq(disjuncts.distinct.map(c => step6(c)))
      case _ => formula
    }
  }

  /**
    * Temp method that handles also empty conjunctions or of size 1
    * @param conjuncts Conjuctions that will be added to and clause if they are more than 1
    * @return Either And of conjuncts, single literal or if seq is empty than True
    */
  def handleConjunctsSeq(conjuncts: Seq[Term]): Term = {
    if (conjuncts.length > 1) {
      And(conjuncts)
    } else if (conjuncts.length == 1) {
      conjuncts.head
    } else {
      True()
    }
  }

  /**
    * Temp method that handles also empty disjunctions or of size 1
    * @param disjuncts Disjuctions that will be added to or clause if they are more than 1
    * @return Either Or of conjuncts, single literal or if seq is empty than False
    */
  def handleDisjunctsSeq(disjuncts: Seq[Term]): Term = {
    if (disjuncts.length > 1) {
      Or(disjuncts)
    } else if (disjuncts.length == 1) {
      disjuncts.head
    } else {
      False()
    }
  }

  /**
    * Calculates all combinations. Used for distributing conjunctions over disjunctions.
    */
  def getCombinations(list: List[List[Term]]): List[List[Term]] = {
    list match {
      case Nil => List()
      case l :: Nil => l.map(e => List(e))
      case l :: ls =>
        val subCombinations = getCombinations(ls)
        subCombinations.flatMap(c => l.map(lItem => lItem :: c))
    }
  }

}