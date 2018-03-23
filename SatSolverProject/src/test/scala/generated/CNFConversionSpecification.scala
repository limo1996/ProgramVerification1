package generated

import generators.{ExhaustivePropositionalFormulaGenerator, RandomPropositionalFormulaGenerator}
import org.scalacheck.Properties
import org.scalacheck.Prop.forAll
import smtlib.parser.Terms.Term
import util.PropositionalLogic
import util.Formula

object CNFConversionSpecification extends Properties("CNFConversion") {

  def check2(f: Term, cf: Term, checker: (Term) => Boolean): Boolean = {
    import solvers.Z3Solver.{checkEntails, checkSAT, checkUnsat}
    checker(cf) && checkEntails(cf, f) && (checkSAT(f).isDefined || checkUnsat(cf))
  }

  property("toCNF:exhaustive") =
    forAll(ExhaustivePropositionalFormulaGenerator.formula) { (f: Term) =>
      check2(f, new Formula(f).toTerm, PropositionalLogic.isCNF)
    }

  property("toCNF:exhaustive - tseitin") =
    forAll(ExhaustivePropositionalFormulaGenerator.formula) { (f: Term) =>
      check2(f, new Formula(f, true).toTerm, PropositionalLogic.isCNF)
    }

  property("toCNF:random") =
    forAll(RandomPropositionalFormulaGenerator.formula) { (f: Term) =>
      check2(f, new Formula(f).toTerm, PropositionalLogic.isCNF)
    }

  property("toCNF:random - tseitin") =
    forAll(RandomPropositionalFormulaGenerator.formula) { (f: Term) =>
      check2(f, new Formula(f, true).toTerm, PropositionalLogic.isCNF)
    }
}