package handwritten


import org.scalatest.FunSuite
import org.scalatest.concurrent.TimeLimitedTests
import org.scalatest.time.{Seconds, Span}
import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier, Term}
import smtlib.theories.Core._
import solvers.DPLL
//import solvers.CDCL
import util.PropositionalLogic

abstract class SolverBaseTest extends FunSuite with TimeLimitedTests {

  def Var(name: String): QualifiedIdentifier = {
    QualifiedIdentifier(SimpleIdentifier(SSymbol(name)))
  }

  override def timeLimit = Span(10, Seconds)

  def compute(formula: Term): Option[Map[String, Boolean]]

  private val n = Var("n")
  private val p = Var("p")
  private val q = Var("q")
  private val r = Var("r")
  private val u = Var("u")
  private val t = Var("t")
  private val s = Var("s")

  test("True is trivially sat") {
    val formula = True()
    compute(formula) match {
      case Some(model) =>
        assert(model.isEmpty)
        assert(PropositionalLogic.evaluate(formula, model))
      case _ => assert(false)
    }
  }

  test("False is trivially unsat") {
    val formula = False()
    assert(compute(formula).isEmpty)
  }

  test("p is sat") {
    val formula = p
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 1)
        assert(model.get("p").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None =>
        assert(false)
    }
  }

  test("!p or true or false is sat") {
    val formula = Or(Not(p), True(), False())
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 1)
        assert(model.get("p").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("p and q is sat") {
    val formula = And(p, q)
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 2)
        assert(model.get("p").contains(true))
        assert(model.get("q").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("p and !p is unsat") {
    val formula = And(p, Not(p))
    assert(compute(formula).isEmpty)
  }

  test("p and (p or q) is sat") {
    val formula = And(p, Or(p, q))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 2)
        assert(model.get("p").contains(true))
        assert(model.get("q").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

test("!p and (!p or q) is sat") {
  val formula = And(Not(p), Or(Not(p), q))
  compute(formula) match {
    case Some(model) =>
      assert(model.size == 2)
      assert(model.get("p").contains(false))
      assert(model.get("q").contains(true))
      assert(PropositionalLogic.evaluate(formula, model))
    case None => assert(false)
  }
}

  test("p and (!p or q) is sat") {
    val formula = And(p, Or(Not(p), q))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 2)
        assert(model.get("p").contains(true))
        assert(model.get("q").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(p or q) and (!p or q) is sat") {
    val formula = And(Or(p, q), Or(Not(p), q))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 2)
        assert(model.get("q").contains(true))
        assert(model.get("p").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(p or q) and (!p or !q) is sat") {
    val formula = And(Or(p, q), Or(Not(p), Not(q)))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 2)
        assert(
          (model.get("q").contains(false) && model.get("p").contains(true)) ||
            (model.get("q").contains(true) && model.get("p").contains(false)))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(p or !q) and (r or !q) is sat") {
    val formula = And(Or(p, Not(q)), Or(r, Not(q)))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 3)
        assert(
          model.get("q").contains(false) ||
            (model.get("p").contains(true) && model.get("r").contains(true))
        )
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(!p or true or true) and (p or !p) is sat") {
    val formula = And(Or(Not(p), True(), True()), Or(p, Not(p)))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 1)
        assert(model.get("p").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(!p or q or true) and (p or true or p) and (r or !q) is sat") {
    val formula = And(Or(Not(p), q, True()), Or(p, True(), p), Or(r, Not(q)))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 3)
        assert(model.get("r").contains(true) || model.get("q").contains(false))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(n or p) and (!n or p or q) and (!n or p or !q) and (!p or r) is sat") {
    val formula = And(Or(n, p), Or(Not(n), p, q), Or(Not(n), p, Not(q)), Or(Not(p), r))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 4)
        assert(model.get("n").contains(true))
        assert(model.get("p").contains(true))
        assert(model.get("q").contains(true))
        assert(model.get("r").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(n or p) and (!n or p or q) and (!n or p or !q) and (!p or r) and (!u or t) and (!r or !s or t) is sat") {
    val formula = And(Or(n, p), Or(Not(n), p, q), Or(Not(n), p, Not(q)), Or(Not(p), r), Or(Not(u), t), Or(Not(r), Not(s), t))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 7)
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(n or p) and (!n or p or q) and (!n or p or !q) and (!p or r) and (!u or t) and (!r or !s or t) and (q or s) and (!p or t or u) and (!p or !t or ! u) and (!r or !t or u) is unsat") {
    val formula = And(Or(n, p), Or(Not(n), p, q), Or(Not(n), p, Not(q)), Or(Not(p), r), Or(Not(u), t), Or(Not(r), Not(s), t), Or(q, s), Or(Not(p), t, u), Or(Not(p), Not(t), Not(u)), Or(Not(r), Not(t), u))
    assert(compute(formula).isEmpty)
  }

  test("(p or true) and (q or !q) and (r or !p or false) is sat") {
    val formula = And(Or(p, True()), Or(q, Not(q)), Or(r, Not(p), False()))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 3)
        assert(model.get("p").contains(false) || model.get("r").contains(true))
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

  test("(and (or true p false) (or (not r) q) (or r false (not q)))") {
    val formula = And(Or(True(), p, False()), Or(Not(r), q), Or(r, False(), Not(q)))
    compute(formula) match {
      case Some(model) =>
        assert(model.size == 3)
        assert(PropositionalLogic.evaluate(formula, model))
      case None => assert(false)
    }
  }

}

class CDCLSuite extends SolverBaseTest {
  override def compute(formula: Term): Option[Map[String, Boolean]] = {
    //CDCL.checkSAT(formula)
    ???
  }
}

class DPLLSuite extends SolverBaseTest {
  override def compute(formula: Term): Option[Map[String, Boolean]] = {
    val v = new DPLL(true)
    v.checkSAT(formula)
  }
}