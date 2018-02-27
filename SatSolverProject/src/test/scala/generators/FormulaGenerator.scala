package generators

import org.scalacheck._
import Gen._
import smtlib.parser.Terms.{QualifiedIdentifier, SSymbol, SimpleIdentifier, Term}
import smtlib.theories.Core._


/**
  * Abstract class with basic formula generators.
  */
abstract class BaseFormulaGenerator(val initialLevel: Int, val variableCount: Int) {

  def Var(name: String): QualifiedIdentifier = {
    QualifiedIdentifier(SimpleIdentifier(SSymbol(name)))
  }

  def formula: Gen[Term] = genTerm(initialLevel)

  def genTerm(level: Int): Gen[Term]

  def genVarName: Gen[String] = for {
    id <- Gen.choose(0, variableCount)
  } yield s"v${id}"

  def genTrue: Gen[Term] = const(True())
  def genFalse: Gen[Term] = const(False())
  def genVar: Gen[Term] = for {
    name <- genVarName
  } yield QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None)
  def genNot(level: Int): Gen[Term] = for {
    term <- genTerm(level)
  } yield Not(term)
  def genOr2(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
  } yield Or(term1, term2)
  def genOr3(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
    term3 <- genTerm(level)
  } yield Or(term1, term2, term3)
  def genAnd2(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
  } yield And(term1, term2)
  def genAnd3(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
    term3 <- genTerm(level)
  } yield And(term1, term2, term3)
  def genImplies(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
  } yield Implies(term1, term2)
  def genEquals(level: Int): Gen[Term] = for {
    term1 <- genTerm(level)
    term2 <- genTerm(level)
  } yield Equals(term1, term2)

}

/**
  * Trait for generating generic propositional formulas.
  */
trait PropositionalFormulaGenerator extends BaseFormulaGenerator {

  override def genTerm(level: Int): Gen[Term] = if (level <= 1)
    lzy(oneOf(genTrue, genFalse, genVar))
  else
    lzy(oneOf(
      genTrue, genFalse, genVar,
      genNot(level - 1),
      genOr2(level - 1), genOr3(level - 1),
      genAnd2(level - 1), genAnd3(level - 1),
      genImplies(level - 1), genEquals(level - 1)
    ))

}

object ExhaustivePropositionalFormulaGenerator
    extends BaseFormulaGenerator(2, 2)
    with PropositionalFormulaGenerator {
}

object RandomPropositionalFormulaGenerator
  extends BaseFormulaGenerator(20, 10)
    with PropositionalFormulaGenerator {
}

/**
  * Trait for generating normalized propositional formulas.
  */
trait NormalizedFormulaGenerator extends BaseFormulaGenerator {

  override def genTerm(level: Int): Gen[Term] = if (level <= 1)
    lzy(oneOf(genTrue, genFalse, genVar))
  else
    lzy(oneOf(
      genTrue, genFalse, genVar,
      genNot(level - 1),
      genOr2(level - 1), genOr3(level - 1),
      genAnd2(level - 1), genAnd3(level - 1)
    ))

}

object ExhaustiveNormalizedFormulaGenerator
    extends BaseFormulaGenerator(2, 2)
    with NormalizedFormulaGenerator {
}

object RandomNormalizedFormulaGenerator
  extends BaseFormulaGenerator(20, 10)
    with NormalizedFormulaGenerator {
}

/**
  * Trait for generating CNF formulas.
  */
trait CNFGenerator extends BaseFormulaGenerator {

  val genVarNot: Gen[Term] = for {
    name <- genVarName
  } yield Not(Var(name))

  val genLit: Gen[Term] = oneOf(genTrue, genFalse, genVar, genVarNot)
  val genOr2: Gen[Term] = for {
    term1 <- genLit
    term2 <- genLit
  } yield Or(term1, term2)
  val genOr3: Gen[Term] = for {
    term1 <- genLit
    term2 <- genLit
    term3 <- genLit
  } yield Or(term1, term2, term3)
  val genAnd2: Gen[Term] = for {
    term1 <- oneOf(genOr2, genOr3)
    term2 <- oneOf(genOr2, genOr3)
  } yield And(term1, term2)
  val genAnd3: Gen[Term] = for {
    term1 <- oneOf(genOr2, genOr3)
    term2 <- oneOf(genOr2, genOr3)
    term3 <- oneOf(genOr2, genOr3)
  } yield And(term1, term2, term3)

  override def genTerm(level: Int): Gen[Term] = oneOf(genOr2, genOr3, genAnd2, genAnd3)

  def literal: Gen[Term] = genLit
  def clause: Gen[Term] = oneOf(genOr2, genOr3)

}

object ExhaustiveCNFGenerator
  extends BaseFormulaGenerator(0, 2)
    with CNFGenerator {
}

object RandomCNFGenerator
  extends BaseFormulaGenerator(0, 100)
    with CNFGenerator {
}

/**
  * Trait for generating CNF formulas without True False.
  */
trait CNFGeneratorVarOnly  extends BaseFormulaGenerator {

  val genVarNot: Gen[Term] = for {
    name <- genVarName
  } yield Not(Var(name))

  val genLit: Gen[Term] = oneOf(genVar, genVarNot)
  val genOr2: Gen[Term] = for {
    term1 <- genLit
    term2 <- genLit
  } yield Or(term1, term2)
  val genOr3: Gen[Term] = for {
    term1 <- genLit
    term2 <- genLit
    term3 <- genLit
  } yield Or(term1, term2, term3)
  val genAnd2: Gen[Term] = for {
    term1 <- oneOf(genOr2, genOr3)
    term2 <- oneOf(genOr2, genOr3)
  } yield And(term1, term2)
  val genAnd3: Gen[Term] = for {
    term1 <- oneOf(genOr2, genOr3)
    term2 <- oneOf(genOr2, genOr3)
    term3 <- oneOf(genOr2, genOr3)
  } yield And(term1, term2, term3)

  override def genTerm(level: Int): Gen[Term] = oneOf(genOr2, genOr3, genAnd2, genAnd3)

  def literal: Gen[Term] = genLit
  def clause: Gen[Term] = oneOf(genOr2, genOr3)

}

object ExhaustiveCNFVarOnlyGenerator
  extends BaseFormulaGenerator(0, 5)
    with CNFGeneratorVarOnly {
}

object RandomCNFVarOnlyGenerator
  extends BaseFormulaGenerator(0, 100)
    with CNFGeneratorVarOnly {
}
