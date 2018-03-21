package solvers

import util.{Event, Formula, ImplicationGraph}

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.util.Random
import smtlib.parser.Terms.Term
import smtlib.parser.Terms

/**
  * A stub of a configurable implementation of the CDCL.
  *
  * @param usePureLiteralRule True if the implementation should use
  *                           the pure literal rule.
  */
class CDCL(override val usePureLiteralRule: Boolean) extends DPLL(usePureLiteralRule) {

  /**
    * All solvers should implement this method to satisfy the common interface.
    */
  override def checkSAT(formula: Terms.Term): Option[Map[String, Boolean]] = {
    /*import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier}
    import smtlib.theories.Core.{And, Not, Or}
    def Var(name: String): QualifiedIdentifier = {
      QualifiedIdentifier(SimpleIdentifier(SSymbol(name)))
    }
    val x = Var("x")
    val a = Var("a")
    val c = Var("c")
    val d = Var("d")
    val formula1 = And(
      Or(x, a, c, d), Or(Not(a), Not(c), d), Or(Not(c), Not(d)), Or(Not(x), c, d),
      Or(c, Not(d)), Or(x, Not(a), c, d), Or(x, a, Not(c), d))
*/
    val cnf = new Formula(formula)
    _cnf = cnf
    _implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
    val result = solve(cnf, _implication_graph)
    println(result.map(_.toMap))
    result.map(_.toMap)
  }

  /**
    * Makes a decision but first checks and applies unit propagation.
    * @param cnf
    * @return
    */
  @tailrec
  final override def decision(cnf: Formula): Boolean = {
    if (check_consistency(cnf)) return true                         // if all clauses are disabled => solved
    if (check_inconsistency(cnf)) {                                 // if there is empty clause => conflict
      if(resolveConflict())                                         // resolve conflict => learn clause, jump back to relevant decision literal
        decision(cnf)                                               // carry on with learned clause
      else
        return false
    } else {
      val (v1, v2) = unit_propagation0(cnf)                         // apply unit propagation recursively
      if (v1) {
        if (v2) return true
        else {
          if(resolveConflict())                                     // resolve conflict => learn clause, jump back to relevant decision literal
            decision(cnf)                                           // carry on with learned clause
          else
            return false
        }
      } else {
        val lit = request_first_unassigned(cnf)
        //val lit = request_literal(cnf)                            // -> working as well

        assert(lit != -1)
        println("CDCL decision on: " + getName(lit))
        _implication_graph.logDecision(lit)
        disable(lit)

        decision(cnf)
      }
    }
  }

  /**
    *
    * @return
    */
  private def resolveConflict() : Boolean = {
    val next_decision = conflictResolution()                  // resolve conflict and return next decision literal to pick
    if (next_decision == -1)                                  // if there are no more decisions to make and model
      return false

    println("Next decision: " + getName(next_decision))
    select_literal(next_decision)                             // select literal
    _implication_graph.logDecision(next_decision)             // log our decision
    disable(next_decision)                                    // disable all occurrences of literal
    true
  }

  private def conflictResolution() : Int = {
    println("Conflict detected!")
    val conflict_lit = _implication_graph.lastEvent().get.getLiteral
    var parents = getAllParentDecisionLiterals(conflict_lit, _implication_graph)
    for(c <- getClauseLiterals(_cnf.Literal.neg(conflict_lit), _implication_graph))
      parents ++= getAllParentDecisionLiterals(_cnf.Literal.neg(c), _implication_graph)
    _cnf.addNewClause(parents.toSeq)        // clause learning

    var relevantDecisions = Set[Int]()
    for (c <- parents)
      relevantDecisions += _cnf.Literal.neg(c)

    //println("Relevant decisions: " + relevantDecisions.map(c => getName(c)))
    //println("Curr problem: " + getName(_implication_graph.lastEvent().get.getLiteral))

    undo_before_event_of_literal1(relevantDecisions)

    //println("Before problem: " + getName(_implication_graph.lastEvent().get.getLiteral))

    /* Idea: recursively iterate to decision which was done not on negated literal. Than return its negation */
    while(_implication_graph.lastEvent().isDefined && _branching(_cnf.Literal.toVariable(_implication_graph.lastEvent().get.getLiteral) - 1) == 2){
      val lit = _implication_graph.lastEvent().get.getLiteral
      relevantDecisions -= lit
      //relevantDecisions ++= _sibling_parents(_cnf.Literal.toVariable(lit) - 1)
      undo_before_event_of_literal1(relevantDecisions)
    }
    if(_implication_graph.lastEvent().isEmpty)
      return -1
    // pop to prev decision event,  redo cnf and return to_solve
    val ev = _implication_graph.lastEvent().get
    println("Problem " + getName(ev.getLiteral))
    val to_solve = _cnf.Literal.neg(ev.getLiteral)
    //deselect_literal(ev.getLiteral)
    enable(ev, _implication_graph)
    _implication_graph.popEvent()
    to_solve
  }

  private def getClauseLiterals(lit: Int, implication_graph: ImplicationGraph) : Seq[Int] = {
    var toReturn : Seq[Int] = ArrayBuffer[Int]()
    _cnf.foreachEnabled(c => {
      if(c.enabledLiteralsCount == 0 && c.literals.contains(_cnf.Literal.disable(lit)))
        toReturn = c.literals
    })
    toReturn
  }

  private def isDecision(event: Event, implication_graph: ImplicationGraph) : Option[Int] = {
    import implication_graph.{Decision, Consequence}
    event match {
      case Decision(i, _) => Some(i)
      case Consequence(i, _) => None
    }
  }

  private def getAllParentDecisionLiterals(lit: Int, implication_graph: ImplicationGraph) : Set[Int] = {
    import implication_graph.{Decision, Consequence}
    val event = implication_graph.getEvent(lit)
    event match {
      case Decision(i, pred) => Set(_cnf.Literal.neg(i))
      case Consequence(i, pred) => {
        var parents = Set[Int]()
        for(p <- pred)
          parents ++= getAllParentDecisionLiterals(p, implication_graph)
        parents
      }
    }
  }

  private def learnClause() : Set[Int] = {
    val conflict_lit = _implication_graph.lastEvent().get.getLiteral
    getAllParentDecisionLiterals(conflict_lit, _implication_graph)
  }


}
