package solvers

import util.{Event, Formula, ImplicationGraph}

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

import smtlib.parser.Terms

final class CDCL(override val usePureLiteralRule: Boolean) extends DPLL(usePureLiteralRule) {
  //protected var implication_graph: ImplicationGraph = null;//= new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
  /**
    * All solvers should implement this method to satisfy the common interface.
    */
  /*override def checkSAT(formula: Terms.Term): Option[Map[String, Boolean]] = {
    val cnf = new Formula(formula)
    _implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
    val result = solve(cnf)
    result.map(_.toMap)

  }*/

  override def solve(cnf: Formula, implication_graph: ImplicationGraph): Option[cnf.Model] = {
    None
  }
}
