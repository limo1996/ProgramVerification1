package solvers

import java.io._

import core.SATSolver
import smtlib.parser.Commands._
import smtlib.parser.Terms.{Identifier, SSymbol, Sort, Term}
import smtlib.theories.Core.{Not, Or}
import util.{Formula, PropositionalLogic}

import scala.sys.process.{Process, ProcessIO, ProcessLogger}

/**
  * Object that wraps the Z3 solver.
  */
object Z3Solver extends SATSolver {

  private lazy val z3_path = {
    sys.env.getOrElse("Z3_EXE", "z3.exe")
  }

  private val bool = Sort(Identifier(SSymbol("Bool"), Seq()))

  private def declareVariable(name: String) = {
    DeclareFun(SSymbol(name), Seq(), bool)
  }

  private def declareVariables(formula: Term) = {
    PropositionalLogic.propositionalVariables(formula) map declareVariable
  }

  private def createInputStream(formula: Term): Stream[Command] = {
    SetOption(ProduceModels(true)) #::
      SetLogic(QF_UF()) #::
      declareVariables(formula).toStream #:::
      Assert(formula) #::
      CheckSat() #::
      //    GetModel() #::
      Stream.empty[Command]
  }

  private def createInput(formula: Term): (OutputStream => Unit) = {
    (stdin: OutputStream) => {
      val printer = new PrintWriter(new BufferedOutputStream(stdin))
      createInputStream(formula).foreach(
        (cmd) => {
          printer.write(cmd.toString())
        }
      )
      printer.close()
    }
  }

  def checkSAT(formula: Formula): Option[formula.Model] = {
    val term = formula.toTerm
    if (checkSAT(term).isDefined) {
      Some(new formula.Model)
    } else {
      None
    }
  }

  def checkSAT(formula: Term): Option[Map[String,Boolean]] = {
    val process = Process(z3_path, Seq("-smt2", "-in"))
    var result: String = null
    val processIO = new ProcessIO(
      createInput(formula),
      stdout => {
        val reader = new BufferedReader(new InputStreamReader(stdout))
        result = reader.readLine()
      },
      stderr => {
        scala.io.Source.fromInputStream(stderr)
          .getLines.foreach(println)
      }
    )
    val handle = process.run(processIO)
    assert(handle.exitValue() == 0)
    assert(result == "sat" || result == "unsat")
    if (result == "sat") {
      Some(Map())
    } else {
      None
    }
  }

  def checkValid(formula: Term): Boolean = {
    checkUnsat(Not(formula))
  }

  def checkUnsat(formula: Term): Boolean = checkSAT(formula).isEmpty

  def checkEntails(formulaA: Term, formulaB: Term): Boolean = {
    checkValid(Or(Not(formulaA), formulaB))
  }

  def checkEquals(formulaA: Term, formulaB: Term): Boolean = {
    checkEntails(formulaA, formulaB) && checkEntails(formulaB, formulaA)
  }

  def checkSAT(file: File): Boolean = {
    val process = Process(z3_path, Seq(file.getPath))
    val buffer = new StringBuffer()
    assert(process ! ProcessLogger(buffer append _) == 0)
    buffer.toString.startsWith("sat")
  }

}
