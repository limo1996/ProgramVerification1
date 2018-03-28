package files

import java.io.File

import core.MySATSolver
import org.scalatest.FunSuite
import org.scalatest.concurrent.TimeLimitedTests
import org.scalatest.time.{Seconds, Span}
import solvers.{SATSolverConfiguration, SolverFactory, SudokuSolver}
import util.PropositionalLogic

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

import smtlib.parser.Commands.Command

/**
  * Sudoku test suite.
  */
class SudokuSuite extends FunSuite with TimeLimitedTests {
  override def timeLimit = Span(30, Seconds)

  private def collectFiles(extension: String) = {
    val paths = mutable.Buffer[File]()

    def collectFiles(file: File): Unit = {
      if (file.exists) {
        if (file.isDirectory) {
          file.listFiles() foreach (
            (subfile) => collectFiles(subfile))
        }
        else if (file.getName.endsWith(extension)) {
          paths.append(file)
        }
      }
    }

    collectFiles(new File(getClass.getResource("/sudoku").toURI.getPath))
    paths
  }

  val sudokuFiles = collectFiles(".txt")

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

  /* Parses file into 9x9 matrix */
  private def parseFile(path: String) : ArrayBuffer[Array[Int]] = {
    val sudoku: ArrayBuffer[Array[Int]] = ArrayBuffer[Array[Int]]()
    for (line <- Source.fromFile(path).getLines) {
      sudoku.append(line.map(c => c.toString.toInt).toArray)
    }
    assert (sudoku.size == 9)
    sudoku
  }

  def checkSudoku(file: String) : Unit = {
    val sudoku = parseFile(file)
    val columnSets = Array.fill(9){Set[Int]()}

    // check for every row that it contains 9 distinct numbers
    for(i <- 0 to 8){
      var rowSet = sudoku(i).toSet
      assert(rowSet.size == 9)
      for(j <- 0 to 8)
        columnSets(j) += sudoku(i)(j)
    }

    // check that each columns has 9 distinct numbers
    for(i <- 0 to 8){
      assert(columnSets(i).size == 9)
    }

    // check that every square has 9 distinct numbers
    for(i <- 0 to 2){
      for(j <- 0 to 2){
        var squareSet = Set[Int]()
        for(x <- 0 to 2){
          for(y <- 0 to 2){
            squareSet += sudoku(3*i + x)(3*j + y)
          }
        }
        assert (squareSet.size == 9)
      }
    }
  }

  sudokuFiles foreach((file) => {
    test(s"CDCLBaseline $file --sudoku") {
      val solver = new SudokuSolver()
      solver.solve(SolverFactory.getConfigurationFromString("CDCLBaseline").get, file.getAbsolutePath)
      val solutionPath = "src/test/resources/solved_sudoku/" + file.getName + ".res"
      checkSudoku(solutionPath)
    }
  })

}
