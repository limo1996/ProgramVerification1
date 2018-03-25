// Please do not modify this file! It will be overwritten during the grading.
package core

import smtlib.parser.Terms.Term
import util.Formula

trait SATSolver {

  // perform satisfiability checking on the given input formula
  // returns None if the formula is unsatisfiable
  // returns Some(m) if the formula is satisfiable, where m should be a Map instance representing
  // a model (mapping the variables to true/false Boolean values
  def checkSAT(formula : Term): Option[Map[String,Boolean]]

  // converts the result from a call to “checkSAT” above into a String representation
  // (according to the SMT-LIB standard)
  def outputResult(res : Option[Map[String,Boolean]], includeModel: Boolean = true) : String =
  // Pattern match on "res"
    res match {
      case None => "unsat"
      case Some(m) =>
        // No need to surround the body of a pattern matching case with curly braces
        // (it's always a code block)
        if (includeModel) {
          m.keySet.foldLeft("sat\n(model\n")(
            (s, key) => s"$s  (define-fun $key () Bool\n    ${m(key)})\n") + ")"
        } else {
          "sat"
        }
    }

  def convertToCNF(formula: Term): Formula = {
    new Formula(formula)
  }
}
