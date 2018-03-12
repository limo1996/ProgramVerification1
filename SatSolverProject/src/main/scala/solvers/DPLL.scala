package solvers

import core.SATSolver
import util.Formula
import smtlib.parser.Terms
import util.{Formula, ImplicationGraph}
import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier}
import smtlib.theories.Core.{And, Not, Or}
import scala.collection.mutable.ArrayBuffer
/**
  * A stub of a configurable implementation of the DPLL.
  *
  * @param usePureLiteralRule True if the implementation should use
  *                           the pure literal rule.
  */
class DPLL(val usePureLiteralRule: Boolean) extends SATSolver {

  var _implication_graph : ImplicationGraph
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
    _implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)

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
      Or(Not(p), Not(t), Not(u)), Or(r, Not(t), u))
    println(formula1)
    val cnf1 = new Formula(formula1)
    val c = applyPureLiteralRule(cnf1)
    c.printDebugToStdout()
    return None
  }

  /*
   * Decision rule. Decision literal chosen ... ???
   */
  private def decision(cnf: Formula) : Boolean = {
    /* TODO: */
    false
  }

  /*
   * Applies pure literal rule to all pure variables found and returns simplified formula.
   */
  private def applyPureLiteralRule(cnf: Formula) : Formula = {
    val usage = ArrayBuffer.fill(cnf.literalCount){(false,false)};                // Create array where index + 1 indicated variable (1 based) and value
    cnf.foreachEnabled(c => {                                                     // is tuple where first value indicated positive appearance and second negative.
      c.foreachEnabled(l => {                                                     // Loop through all clauses and variables in them
        val variable : Int = cnf.Literal.toVariable(l) - 1;                       // get variable index
        val use = usage(variable)                                                 // get initial value
        usage(variable) = (use._1 || !cnf.Literal.isNegated(l), use._2 || cnf.Literal.isNegated(l));
      })                                                                          // set appropriate flag to appropriate value
    })

    var i = 1                                                                     // create counter
    for(l <- usage){                                                              // loop through the flag array
      if((l._1 && !l._2) || (!l._1 && l._2)){                                     // if variable occurs only positively or negatively
        var lit : cnf.Literal = i                                                 // reconstruct literal from index
        if(!l._1)
            lit = cnf.Literal.neg(i)                                              // if negated negate
        cnf.foreachEnabled(c => {                                                 // loop through all clauses
          if(c.literals.contains(lit)) {                                          // if clause contains pure literal
            c.enabled = false;                                                    // disable the clause
          }
        })
      }
      i+=1                                                                        // increment the counter
    }
    cnf
  }

  /*
   * Applies unit propagation rule on formula and returns simplified formula.
   */
  private def applyUnitPropagation(cnf: Formula) : Formula = {
    var literals = new ArrayBuffer[cnf.Literal]()                                 // Array that contains literals involved in unit propagation.
    cnf.foreachEnabled(c =>                                                       // Loop through all clauses.
      if(c.enabledLiteralsCount == 1){                                            // If clause contains just one literal -> unit clause.
        val i = 0
        while (i < c.literals.length) {                                           // Push literal from clause into our array.
          if (cnf.Literal.isEnabled(c.literals(i)))
            literals += c.literals(i)
        }
      }
    )
    /* TODO: */
    cnf.foreachEnabled(c => {
      if (c.literals.contains(l => literals.contains(l)))
        c.enabled = false

      if (c.literals.contains(l => literals.contains(cnf.Literal.neg(l))))
        c.enabled = false

    })
    cnf
  }
}
