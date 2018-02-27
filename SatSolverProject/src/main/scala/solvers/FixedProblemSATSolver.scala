package solvers

import core.SATSolver
import smtlib.parser.Terms.Term
import util.{Formula, ImplicationGraph}

import scala.collection.mutable.ArrayBuffer

// A SAT solver that ignores the input formula and instead shows how to use the
// implication graph on a problem from the exercise sheet 2.
object FixedProblemSATSolver extends SATSolver {

  private def solve(cnf: Formula): Option[cnf.Model] = {
    // Below is an example how the implication graph could be used.

    // The example formula given in the class.
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
    val formula = And(
      Or(n, p), Or(Not(n), p, q), Or(Not(n), p, Not(q)), Or(Not(p), r),
      Or(Not(u), t), Or(Not(r), Not(s), t), Or(q, s), Or(Not(p), t, u),
      Or(Not(p), Not(t), Not(u)), Or(Not(r), Not(t), u))
    val cnfFormula = new Formula(formula)
    val nVar = cnfFormula.getVariableFromName("n")
    val pVar = cnfFormula.getVariableFromName("p")
    val qVar = cnfFormula.getVariableFromName("q")
    val rVar = cnfFormula.getVariableFromName("r")
    val uVar = cnfFormula.getVariableFromName("u")
    val tVar = cnfFormula.getVariableFromName("t")
    val sVar = cnfFormula.getVariableFromName("s")

    // The implication graph to use with the constructed formula.
    val graph = new ImplicationGraph(cnfFormula.literalCount, cnfFormula, verbose = true)
    // Let's get into the state shown on the slide.
    import cnfFormula.Variable.{toNegatedLiteral, toLiteral}
    graph.logDecision(toLiteral(nVar))
    // After each log event you would normally also update the formula and log these updates
    // so that you can roll them back later:
    cnfFormula.clauses(0).enabled = false
    graph.lastEvent().get.registerDisabledClause(0)
    cnfFormula.clauses(1).disableLiteral(0)
    graph.lastEvent().get.registerDisabledLiteral(1, 0)
    cnfFormula.clauses(2).disableLiteral(0)
    graph.lastEvent().get.registerDisabledLiteral(2, 0)
    // All effects are logged in the effects array:
    println(graph.lastEvent().get.effects)

    // To print the modified formula, use:
    cnfFormula.printDebugToStdout()
    // Disabled literals and clauses are marked with “!”.

    // Since updating formula manually is very verbose we will skip this for the
    // rest of the example.

    graph.logDecision(toLiteral(pVar))
    graph.logConsequence(toLiteral(rVar), ArrayBuffer(toLiteral(pVar)))
    graph.logDecision(toNegatedLiteral(sVar))
    graph.logConsequence(toLiteral(qVar), ArrayBuffer(toNegatedLiteral(sVar)))
    graph.logDecision(toLiteral(tVar))
    graph.logConsequence(toLiteral(uVar), ArrayBuffer(toLiteral(rVar), toLiteral(tVar)))
    // Since we already reached a conflict, there is no point in logging ¬u and
    // the graph implementation asserts that no variable is logged more than once.
    //graph.logConsequence(toNegatedLiteral(uVar), ArrayBuffer(toLiteral(pVar), toLiteral(tVar)))

    // Let's write the graph as a graphviz file. You can use “dot -Tps graph1.dot -O” to render it.
    graph.writeAsDot("/data/graph1.dot", Seq(toLiteral(uVar)))

    // Let's perform back-jumping: roll back up to p, and add ¬t.
    graph.popEvent()
    graph.popEvent()
    graph.popEvent()
    graph.popEvent()
    graph.logDecision(toNegatedLiteral(tVar))
    graph.writeAsDot("/data/graph2.dot", Seq(toNegatedLiteral(tVar)))

    ???
  }

  override def checkSAT(formula: Term): Option[Map[String,Boolean]] = {
    val cnf = new Formula(formula)
    val result = solve(cnf)
    result.map(_.toMap)
  }
}
