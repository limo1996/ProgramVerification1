package solvers

import core.SATSolver
import util.Formula
import smtlib.parser.Terms
import util.{Formula, ImplicationGraph}
import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier}
import smtlib.theories.Core.{And, Not, Or}
import scala.collection.mutable.ArrayBuffer
import scala.util.control.Breaks._
/**
  * A stub of a configurable implementation of the DPLL.
  *
  * @param usePureLiteralRule True if the implementation should use
  *                           the pure literal rule.
  */
class DPLL(val usePureLiteralRule: Boolean) extends SATSolver {

  /**
    * All solvers should implement this method to satisfy the common interface.
    */
  override def checkSAT(formula: Terms.Term): Option[Map[String, Boolean]] = {
    val cnf = new Formula(formula)
    val result = solve(cnf)
    result.map(_.toMap)
  }

  /**
    * The method that does the actual work.
    *
    * TODO: Implement.
    */
  private def solve(cnf: Formula): Option[cnf.Model] = {
    /* TEST DATA */
    println("In solve...")

    def Var(name: String): QualifiedIdentifier = {
      QualifiedIdentifier(SimpleIdentifier(SSymbol(name)))
    }

    val n = Var("n")
    val p = Var("p")
    val q = Var("q")
    val r = Var("r")
    val u = Var("u")
    val t = Var("t")
    val s = Var("s")
    val formula1 = And(
      Or(n, p), Or(n, p, q), Or(n, p, Not(q)), Or(Not(p), r),
      Or(Not(u), t), Or(r, Not(s), t), Or(q, s), Or(Not(p), t, u),
      Or(Not(p), Not(t), Not(u), Not(s)), Or(r, Not(t), u), s)
    println(formula1)
    val cnf1 = new Formula(formula1)
    var _implication_graph = new ImplicationGraph(cnf1.literalCount, cnf1, verbose = true)

    /*
     * Decision rule. Decision literal chosen ... ???
     */
    def decision(cnf: Formula): Boolean = {
      /* TODO: */
      val lit_to_decide = cnf.clauses(0).literals(0)
      _implication_graph.logDecision(lit_to_decide)
      false
    }

    /*
     * Applies pure literal rule to all pure variables found and returns simplified formula.
     */
    def applyPureLiteralRule(cnf: Formula): Formula = {
      val usage = ArrayBuffer.fill(cnf.literalCount) {(false, false)};        // Create array where index + 1 indicated variable (1 based) and value
      cnf.foreachEnabled(c => {                                               // is tuple where first value indicated positive appearance and second negative.
        c.foreachEnabled(l => {                                               // Loop through all clauses and variables in them
          val variable: Int = cnf.Literal.toVariable(l) - 1;                  // get variable index
          val use = usage(variable)                                           // get initial value
          usage(variable) = (use._1 || !cnf.Literal.isNegated(l), use._2 || cnf.Literal.isNegated(l));
        })                                                                    // set appropriate flag to appropriate value
      })

      var i = 1                                                               // create counter
      for (l <- usage) {                                                      // loop through the flag array
        if ((l._1 && !l._2) || (!l._1 && l._2)) {                             // if variable occurs only positively or negatively
          var lit: cnf.Literal = i                                            // reconstruct literal from index
          if (!l._1)
            lit = cnf.Literal.neg(i)                                          // if negated negate
          var j = 0
          cnf.clauses.foreach(c => {                                          // loop through all clauses
            if (c.enabled && c.literals.contains(lit)) {                      // if clause contains pure literal
              c.enabled = false;                                              // disable the clause
              //_implication_graph.lastEvent().get.registerDisabledClause(j)
            }
            j += 1
          })
        }
        i += 1                                                                // increment the counter
      }
      cnf
    }

    /*
     * Applies unit propagation rule on formula and returns simplified formula.
     */
    def applyUnitPropagation(cnf: Formula): Formula = {
      var literals = new ArrayBuffer[cnf.Literal]()                           // Array that contains literals involved in unit propagation.
      var i = 0
      cnf.clauses.foreach(c => {                                              // Loop through all clauses.
        if (c.enabled && c.enabledLiteralsCount == 1) {                       // If clause contains just one literal -> unit clause.
          var j = 0
          while (j < c.literals.length) {                                     // Push literal from clause into our array.
            if (cnf.Literal.isEnabled(c.literals(j)))
              literals += c.literals(j)
            j += 1
          }
        }
        i += 1
      })
      i = 0
      cnf.clauses.foreach(c => {                                              // Now loop through all clauses
        if (c.enabled) {                                                      // If clause is enabled
          for (lit <- literals) {                                             // Go through all pure literals
            if(c.literals.contains(lit)){                                     // If clause contains one of them mark it as disabled
              c.enabled = false
              //_implication_graph.lastEvent().get.registerDisabledClause(i)  // log to implication graph
            } else {                                                          // otherwise
              var j = 0
              for (lit2 <- c.literals) {                                      // go through all literals in clause
                if (lit2 == cnf.Literal.neg(lit)) {                           // if there is negated literal
                  c.literals(j) = cnf.Literal.disable(lit2)                   // than disable it and log to implication graph
                  //_implication_graph.lastEvent().get.registerDisabledLiteral(i, j)
                }
                j += 1
              }
            }
          }
        }
        i += 1
      })
      cnf
    }

    /* TEST */
    val c = applyUnitPropagation(applyPureLiteralRule(cnf1))
    c.printDebugToStdout()
    return None
  }
}
