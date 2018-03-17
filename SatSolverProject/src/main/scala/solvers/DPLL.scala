package solvers

import core.SATSolver
import util.{Event, Formula, ImplicationGraph}
import smtlib.parser.Terms

import scala.util.Random
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer

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
    val implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
    val used_literals = ArrayBuffer.fill(cnf.literalCount) {false}

    import cnf.{Variable, Literal, Model}
    import implication_graph.{DisableClause, DisableLiteral}

    val model = new Model()

    /*
     * Decision rule. Decision literal chosen ... ???
     */
    def decision(cnf: Formula): Boolean = {
      if (check_consistency(cnf)) return true
      if (check_inconsistency(cnf)) return false

      val (v1, v2) = unit_propagation0(cnf)
      if (v1) return v2

      val lit = request_literal(cnf)
      val neg_lit = Literal.neg(lit)

      implication_graph.logDecision(lit)
      disable(cnf, lit)

      if (decision(cnf)) true
      else {
        undo_before_event_of_literal(lit)

        implication_graph.logDecision(neg_lit)
        disable(cnf, neg_lit)

        if (decision(cnf)) true
        else {
          undo_before_event_of_literal(neg_lit)
          deselect_literal(lit)
          false
        }
      }
    }

    def undo_before_event_of_literal(lit: Literal): Unit = {
      val ev1 = implication_graph.getEvent(lit)
      var ev = implication_graph.lastEvent().get
      while (ev != ev1) {
        deselect_literal(ev.getLiteral)
        enable(cnf, ev)
        implication_graph.popEvent()
        ev = implication_graph.lastEvent().get
      }
      enable(cnf, ev1)
      implication_graph.popEvent()
    }

    def find_unit_clause(cnf: Formula) : Option[(Literal, ArrayBuffer[Literal])] = {
      cnf.foreachEnabled(c => {
        if (c.enabledLiteralsCount == 1) {
          val ls = c.literals.clone()
          var unit: Literal = -1                              // will get assigned an actual literal value
          ls.zipWithIndex.foreach({ case(l, idx) =>
            if (cnf.Literal.isEnabled(l)) unit = l
            else ls(idx) = Literal.neg(ls(idx))
          })
          return Some((unit, ls - unit))
        }
      })
      None
    }

    def unit_propagation0(cnf:Formula): (Boolean, Boolean) = {
      val unit = find_unit_clause(cnf)
      if (unit.isDefined) {
        val (lit, preds) = unit.get
        unit_propagation_step(cnf, lit, preds)
      } else (false, false)
    }

    @tailrec
    def unit_propagation_step(cnf: Formula, lit: Literal, preds: ArrayBuffer[Literal]): (Boolean, Boolean) = {
      select_literal(lit)
      implication_graph.logConsequence(lit, preds)
      disable(cnf, lit)

      if (check_consistency(cnf)) return (true, true)
      if (check_inconsistency(cnf)) return (true, false)

      val unit = find_unit_clause(cnf)
      if (unit.isDefined) {
        val (lit, preds) = unit.get
        unit_propagation_step(cnf, lit, preds)
      } else (false, false)
    }

    def check_consistency(formula: Formula): Boolean = {
      for (clause <- formula.clauses)
        if (clause.enabled) return false
      true
    }

    def check_inconsistency(formula: Formula): Boolean = {
      for (clause <- formula.clauses)
        if (clause.enabledLiteralsCount == 0) return true
      false
    }

    def add_rest(formula: Formula): Unit = {
      for (i <- used_literals.indices)
        if (!used_literals(i)) {
          model.addLiteral(Variable.toLiteral(i+1))
        }
    }

    def request_literal(formula: Formula): Literal = {
      var idx = Random.nextInt(used_literals.size)
      while (used_literals(idx))
        idx = Random.nextInt(used_literals.size)
      used_literals(idx) = true
      val lit = Variable.toLiteral(idx+1)
      if (Random.nextInt() % 2 == 1) lit
      else Literal.neg(lit)
    }

    def select_literal(literal: Literal): Unit = {
      used_literals(Literal.toVariable(literal)-1) = true
    }

    def deselect_literal(literal: Literal): Unit = {
      used_literals(Literal.toVariable(literal)-1) = false
    }

    def disable(formula: Formula, literal: cnf.Literal): Unit = {
      formula.clauses.zipWithIndex.foreach({ case(clause, c_idx) =>
        if (clause.enabled && clause.literals.contains(literal)) {
          clause.enabled = false
          implication_graph.logDisableClause(c_idx)
        } else {
          clause.literals.zipWithIndex.foreach({ case (lit, l_idx) =>
            if (cnf.Literal.isEnabled(clause.literals(l_idx)) && cnf.Literal.neg(literal) == lit) {
              clause.disableLiteral(l_idx)
              implication_graph.logDisableLiteral(c_idx, l_idx)
            }
          })
        }
      })
    }

    def enable(formula: Formula, event: Event): Unit = {
      event.effects.foreach({
        case DisableClause(i) => formula.clauses(i).enabled = true
        case DisableLiteral(i, j) => formula.clauses(i).enableLiteral(j)
      })
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
          usage(variable) = (use._1 || !cnf.Literal.isNegated(l), use._2 || cnf.Literal.isNegated(l))
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

    if (decision(cnf)) {
      import implication_graph.{Decision, Consequence}
      while (implication_graph.nonEmpty) {
        val ev = implication_graph.lastEvent().get
        ev match {
          case Decision(i, _) => model.addLiteral(i)
          case Consequence(i, _) => model.addLiteral(i)
        }
        implication_graph.popEvent()
      }
      add_rest(cnf)
      Some(model)
    } else None
  }
}
