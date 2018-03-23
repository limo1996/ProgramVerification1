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
  * @param useTseitinConversion Indicates whether to use tseitin conversion or not.
  */
class DPLL(val usePureLiteralRule: Boolean, val useTseitinConversion : Boolean) extends SATSolver {

  protected var _implication_graph : ImplicationGraph = null;
  protected var _cnf : Formula = null;
  protected var _used_literals : ArrayBuffer[Boolean] = null;
  protected var _branching : ArrayBuffer[Int] = null;
  protected var _sibling_parents : ArrayBuffer[Set[Int]] = null
  /**
    * All solvers should implement this method to satisfy the common interface.
    */
  override def checkSAT(formula: Terms.Term): Option[Map[String, Boolean]] = {
    val cnf = new Formula(formula, useTseitinConversion)
    _cnf = cnf
    _implication_graph = new ImplicationGraph(cnf.literalCount, cnf, verbose = true)
    val result = solve(cnf, _implication_graph)
    result.map(_.toMap)
  }

  /**
    * The method that does the actual work.
    *
    * TODO: Implement.
    */
  protected def solve(cnf: Formula, implication_graph: ImplicationGraph): Option[cnf.Model] = {
    import cnf.{Variable, Literal, Model}
    _used_literals = ArrayBuffer.fill(cnf.literalCount) {false}
    _branching = ArrayBuffer.fill(cnf.literalCount){0}
    _sibling_parents = ArrayBuffer.fill(cnf.literalCount){Set[Int]()}
    var model = new Model()

    if (decision(cnf)) {
      import implication_graph.{Decision, Consequence}
      while (_implication_graph.nonEmpty) {
        val ev = _implication_graph.lastEvent().get
        ev match {
          case Decision(i, _) => model.addLiteral(i)
          case Consequence(i, _) => model.addLiteral(i)
        }
        _implication_graph.popEvent()
      }

      for (i <- _used_literals.indices) {
        if (!_used_literals(i)) {
          model.addLiteral(cnf.Variable.toLiteral(i + 1))
        }
      }
      Some(model)
    } else None
  }
    /*
     * Decision rule. Decision literal chosen ... ???
     */
    protected def decision(cnf: Formula): Boolean = {
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
        undo_before_event_of_literal(Set(lit))

        _implication_graph.logDecision(neg_lit)
        disable(neg_lit)

        if (decision(cnf)) true
        else {
          undo_before_event_of_literal(Set(neg_lit))
          deselect_literal(lit)
          false
        }
      }
    }

  protected def undo_before_event_of_literal(lits: Set[Int]): Unit = {
    val ev = undo_before_event_of_literal1(lits)
    enable(ev, _implication_graph)
    _implication_graph.popEvent()
  }

    protected def undo_before_event_of_literal1(lits: Set[Int]): Event = {
      var evArr = ArrayBuffer[Event]()
      for(l <- lits) {
        //println(_cnf.variableNames(_cnf.Literal.toVariable(l)))
        if(_implication_graph.containsEvent(l))
          evArr += _implication_graph.getEvent(l)
      }

      var ev = _implication_graph.lastEvent().get
      while (!evArr.contains(ev)) {
        deselect_literal(ev.getLiteral)
        enable(ev, _implication_graph)
        _implication_graph.popEvent()
        val tmp_ev = _implication_graph.lastEvent()
        if(tmp_ev.isDefined)
          ev = tmp_ev.get
        else
          return ev
      }
      ev
      //enable(ev, _implication_graph)
      //_implication_graph.popEvent()
    }

    protected def find_unit_clause(cnf: Formula) : Option[(Int, ArrayBuffer[Int])] = {
      cnf.foreachEnabled(c => {
        if (c.enabledLiteralsCount == 1) {
          val ls = c.literals.clone()
          var unit: Int = -1                              // will get assigned an actual literal value
          ls.zipWithIndex.foreach({ case(l, idx) =>
            if (cnf.Literal.isEnabled(l)) unit = l
            else ls(idx) = _cnf.Literal.neg(ls(idx))
          })
          //println("Unit propagation on " + getName(unit))
          return Some((unit, ls - unit))
        }
      })
      None
    }

    protected def unit_propagation0(cnf:Formula): (Boolean, Boolean) = {
      val unit = find_unit_clause(cnf)
      if (unit.isDefined) {
        val (lit, preds) = unit.get
        unit_propagation_step(lit, preds)
      } else (false, false)
    }

  protected def getName(literal: Int) : String = {
    var res = ""
    if(_cnf.Literal.isNegated(literal))
      res += "!"

    res += _cnf.variableNames(_cnf.Literal.toVariable(literal))
    res
  }

    @tailrec
    private def unit_propagation_step(lit: Int, preds: ArrayBuffer[Int]): (Boolean, Boolean) = {
      select_literal(lit)
      _implication_graph.logConsequence(lit, preds)
      disable(lit)

      if (check_consistency(_cnf)) return (true, true)
      if (check_inconsistency(_cnf)) return (true, false)

      val unit = find_unit_clause(_cnf)
      if (unit.isDefined) {
        val (lit, preds) = unit.get
        unit_propagation_step(lit, preds)
      } else (false, false)
    }

    protected def check_consistency(formula: Formula): Boolean = {
      for (clause <- formula.clauses)
        if (clause.enabled) return false
      true
    }

    protected def check_inconsistency(formula: Formula): Boolean = {
      for (clause <- formula.clauses)
        if (clause.enabledLiteralsCount == 0) return true
      false
    }

    protected def request_literal(formula: Formula): Int = {
      var idx = Random.nextInt(_used_literals.size)
      while (_used_literals(idx))
        idx = Random.nextInt(_used_literals.size)
      //_used_literals(idx) = true
      val lit = formula.Variable.toLiteral(idx+1)
      select_literal(lit)
      if (Random.nextInt() % 2 == 1) lit
      else formula.Literal.neg(lit)
    }

  /**
    * Finds and returns first unassigned literal. In case no suchh literal exists returns -1.
    * @param formula from which will be literal chosen
    * @return first unassigned literal
    */
    protected def request_first_unassigned(formula: Formula): Int = {
      for(c <- formula.clauses){
        if(c.enabled) {
          for (l <- c.literals){
            if (_cnf.Literal.isEnabled(l)/*!_used_literals(formula.Literal.toVariable(l) - 1)*/) {
              select_literal(l)
              return l
            }
          }
        }
      }
      return -1
    }

    protected def select_literal(literal: Int): Unit = {
      val idx = _cnf.Literal.toVariable(literal)-1
      _used_literals(idx) = true
      _branching(idx) += 1
    }

    protected def deselect_literal(literal: Int): Unit = {
      val idx = _cnf.Literal.toVariable(literal)-1
      _used_literals(idx) = false
      _branching(idx) = 0
    }

    protected def disable(literal: Int): Unit = {
      _cnf.clauses.zipWithIndex.foreach({ case(clause, c_idx) =>
        if (clause.enabled && clause.literals.contains(literal)) {
          clause.enabled = false
          _implication_graph.logDisableClause(c_idx)
        } else {
          clause.literals.zipWithIndex.foreach({ case (lit, l_idx) =>
            if (_cnf.Literal.isEnabled(clause.literals(l_idx)) && _cnf.Literal.neg(literal) == lit) {
              clause.disableLiteral(l_idx)
              _implication_graph.logDisableLiteral(c_idx, l_idx)
            }
          })
        }
      })
    }

    protected def enable(event: Event, implication_graph: ImplicationGraph): Unit = {
      event.effects.foreach({
        case implication_graph.DisableClause(i) => _cnf.clauses(i).enabled = true
        case implication_graph.DisableLiteral(i, j) => _cnf.clauses(i).enableLiteral(j)
      })
    }

    /*
     * Applies pure literal rule to all pure variables found and returns simplified formula.
     */
    protected def applyPureLiteralRule(): Unit = {
      val usage = ArrayBuffer.fill(_cnf.literalCount) {(false, false)};       // Create array where index + 1 indicated variable (1 based) and value
      _cnf.foreachEnabled(c => {                                              // is tuple where first value indicated positive appearance and second negative.
        c.foreachEnabled(l => {                                               // Loop through all clauses and variables in them
          val variable: Int = _cnf.Literal.toVariable(l) - 1;                 // get variable index
          val use = usage(variable)                                           // get initial value
          usage(variable) = (use._1 || !_cnf.Literal.isNegated(l), use._2 || _cnf.Literal.isNegated(l))
        })                                                                    // set appropriate flag to appropriate value
      })

      var i = 1                                                               // create counter
      for (l <- usage) {                                                      // loop through the flag array
        if ((l._1 && !l._2) || (!l._1 && l._2)) {                             // if variable occurs only positively or negatively
          var lit             = i                                             // reconstruct literal from index
          if (!l._1)
            lit = _cnf.Literal.neg(i)                                         // if negated negate
          var j = 0
          _cnf.clauses.foreach(c => {                                         // loop through all clauses
            if (c.enabled && c.literals.contains(lit)) {                      // if clause contains pure literal
              c.enabled = false;                                              // disable the clause
              _implication_graph.lastEvent().get.registerDisabledClause(j)
            }
            j += 1
          })
        }
        i += 1                                                                // increment the counter
      }
    }
}
