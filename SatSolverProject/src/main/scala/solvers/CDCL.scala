package solvers

import util.{Event, Formula, ImplicationGraph}

import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.util.Random
import smtlib.parser.Terms.Term
import smtlib.parser.Terms

class CDCL(override val usePureLiteralRule: Boolean) extends DPLL(usePureLiteralRule) {

  /*protected override def decision(cnf: Formula): Boolean = {
    if (check_consistency(cnf)) return true
    if (check_inconsistency(cnf)) return false

    val (v1, v2) = unit_propagation0(cnf)
    if (v1) return v2

    val lit = request_literal(cnf)
    val neg_lit = cnf.Literal.neg(lit)

    _implication_graph.logDecision(lit)
    disable(lit)

    if (decision(cnf)) true
    else {
      // resolve conflict -> learn clause, jump back to relevant decision literal
      val next_decision = conflictResolution()

      select_literal(next_decision)
      _implication_graph.logDecision(next_decision)
      disable(next_decision)

      decision(cnf)
    }
  }*/
  override def checkSAT(formula: Terms.Term): Option[Map[String, Boolean]] = {
    import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier}
    import smtlib.theories.Core.{And, Not, Or}
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
      Or(n, p), Or(Not(n), p, q), Or(Not(n), p, Not(q)), Or(Not(p), r),
      Or(Not(u), t), Or(Not(r), Not(s), t), Or(q, s), Or(Not(p), t, u),
      Or(Not(p), Not(t), Not(u)), Or(Not(r), Not(t), u))
    val cnf = new Formula(formula)
    //println("CDCL: solving " + formula1)
    _cnf = cnf
    _implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
    val result = solve(cnf, _implication_graph)
    result.map(_.toMap)
  }

  @tailrec
  final override def decision(cnf: Formula): Boolean = {
    //println(_branching)
    if (check_consistency(cnf)) return true                         // if all clauses are disabled => solved
    if (check_inconsistency(cnf)) {                                 // if there is empty clause => conflict
      // resolve conflict => learn clause, jump back to relevant decision literal
      val next_decision = conflictResolution()                      // resolve conflict and return next decision literal to pick
      //println("Next decision: " + getName(next_decision))
      if (next_decision == -1)                                      // if there are no more decisions to make and model
        return false                                                // was not found there is no solution

      select_literal(next_decision)                                 // select literal
      _implication_graph.logDecision(next_decision)                 // log our decision
      disable(next_decision)                                        // disable all occurrences of literal

      decision(cnf)                                                 // carry on with this decision and return result of it
    } else {
      val (v1, v2) = unit_propagation0(cnf)                         // apply unit propagation recursively
      if (v1) {
        if (v2) return v2
        else {
          // resolve conflict => learn clause, jump back to relevant decision literal
          val next_decision = conflictResolution()                  // resolve conflict and return next decision literal to pick
          //println("Next decision: " + getName(next_decision))
          if (next_decision == -1)                                  // if there are no more decisions to make and model
            return false                                            // was not found there is no solution

          select_literal(next_decision)                             // select literal
          _implication_graph.logDecision(next_decision)             // log our decision
          disable(next_decision)                                    // disable all occurrences of literal

          decision(cnf)                                             // carry on with this decision and return result of it
        }
      } else {
        val lit = request_first_unassigned(cnf)
        //val lit = request_literal(cnf) // -> working as well

        assert(lit != -1)
        //println("CDCL decision on: " + getName(lit))
        _implication_graph.logDecision(lit)
        disable(lit)

        decision(cnf)
      }
    }
  }

  private def conflictResolution() : Int = {
    //println("Conflict detected!")
    val conflict_lit = _implication_graph.lastEvent().get.getLiteral
    var parents = getAllParentDecisionLiterals(conflict_lit, _implication_graph)
    for(c <- getClauseLiterals(_cnf.Literal.neg(conflict_lit), _implication_graph))
      parents ++= getAllParentDecisionLiterals(_cnf.Literal.neg(c), _implication_graph)
    _cnf.addNewClause(parents.toSeq)        // clause learning

    var relevantDecisions = ArrayBuffer[Int]()
    for (c <- parents)
      relevantDecisions += _cnf.Literal.neg(c)

    //println("Relevant decisions: " + relevantDecisions.map(c => getName(c)))
    //println("Curr problem: " + getName(_implication_graph.lastEvent().get.getLiteral))

    undo_before_event_of_literal1(relevantDecisions)

    //println("Before problem: " + getName(_implication_graph.lastEvent().get.getLiteral))

    /* Idea: recursively iterate to decision which was done not on negated literal. Than return its negation */
    while(_implication_graph.lastEvent().isDefined && _branching(_cnf.Literal.toVariable(_implication_graph.lastEvent().get.getLiteral) - 1) == 2){
      relevantDecisions -= _implication_graph.lastEvent().get.getLiteral
      undo_before_event_of_literal1(relevantDecisions)
    }
    if(_implication_graph.lastEvent().isEmpty)
      return -1
    // pop to prev decision event,  redo cnf and return to_solve
    val ev = _implication_graph.lastEvent().get
    //println("Problem " + getName(ev.getLiteral))
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
