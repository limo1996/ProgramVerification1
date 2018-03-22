// Please do not modify this file! It will be overwritten during the grading.
package files

import java.io.File

import CNF2SMTLIB.CNF2SMTLIBv2Converter
import core.MySATSolver
import org.scalatest.FunSuite
import org.scalatest.concurrent.TimeLimitedTests
import org.scalatest.time.{Seconds, Span}
import smtlib.parser.Commands.Command
import solvers.{SATSolverConfiguration, SolverFactory, Z3Solver}
import util.PropositionalLogic

import scala.collection.mutable

/**
  * A base class for collecting all example tests.
  */
class FileSuite extends FunSuite with TimeLimitedTests {
  override def timeLimit = Span(40, Seconds)

  private def collectFiles(extension: String) = {
    val paths = mutable.Buffer[File]()

    def collectFiles(file: File): Unit = {
      if (file.exists) {
        if (file.isDirectory) {
          file.listFiles() foreach (
            (subfile) => collectFiles(subfile))
        }
        else if (file.getName.endsWith(extension) && !file.getName.endsWith("te_10.smt2") && !file.getName.endsWith("op_10.cnf")
                  /*&& !file.getName.endsWith("000.smt2") && !file.getName.endsWith("te_10.smt2")*/) {
          paths.append(file)
        }
      }
    }

    collectFiles(new File(getClass.getResource("/examples").toURI.getPath))
    collectFiles(new File(getClass.getResource("/tests").toURI.getPath))
    paths
  }

  val allCnfFiles = collectFiles(".cnf")
  val allSmtFiles = collectFiles(".smt2")

  def check(z3Result: Boolean, inputString: String, solverType: SATSolverConfiguration): Unit = {
    val script: List[Command] = MySATSolver.parseInputString(inputString)
    val (_, formula) = util.InputProcessing.processCommands(script)
    val solver = SolverFactory.constructSolver(solverType)
    val result = solver.checkSAT(formula)
    result match {
      case None =>
        assert(!z3Result)
      case Some(model) =>
        assert(z3Result)
        assert(PropositionalLogic.evaluate(formula, model))
    }
  }

  allCnfFiles foreach ((file) => {
    SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
      if (solverType != solvers.Z3) {
        test(s"$solverType $file") {
          val z3Result = Z3Solver.checkSAT(file)
          val converter = new CNF2SMTLIBv2Converter
          val inputString = converter.convertDimacs(file.getAbsolutePath)
          check(z3Result, inputString, solverType)
        }
      }
    })
  })

  allSmtFiles foreach ((file) => {
    SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
      if (solverType != solvers.Z3) {
        test(s"$solverType $file") {
          val z3Result = Z3Solver.checkSAT(file)
          val inputString = {
            val source = scala.io.Source.fromFile(file)
            try source.mkString finally source.close()
          }
          check(z3Result, inputString, solverType)
        }
      }
    })
  })

}
