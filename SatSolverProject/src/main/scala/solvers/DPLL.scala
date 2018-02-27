package solvers

import core.SATSolver
import smtlib.parser.Terms
import util.Formula

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
  private def solve(cnf: Formula): Option[cnf.Model] = ???

}
