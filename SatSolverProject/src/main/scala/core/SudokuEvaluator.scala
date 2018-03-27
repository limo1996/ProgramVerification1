package core

import java.util.concurrent.Executors
import scala.concurrent.duration._

import solvers.{SolverFactory, SudokuSolver}

class SudokuEvaluator extends Evaluator {
  override protected val runs = 10                         // # experiments for every configuration
  override protected val timeout = 60000                   // max duration in which an experiment should terminate

  override def run(): Unit = {
    val dirPathsToPrefixes = Map("sudoku" -> "Sudoku_")
    val solverToWriter = createOutputFiles(dirPathsToPrefixes)

    dirPathsToPrefixes.foreach{ case(dirPath, prefix) =>
      val files = collectFiles(dirPath, ".txt")
      files foreach ((file) => {
        println(file.toString)
        val sudokuSolver = new SudokuSolver()
        val formula = sudokuSolver.produceFormula(file.getAbsolutePath)

        SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
          val solver = SolverFactory.constructSolver(solverType)
          val result = averagedExperiment(solver, formula)
          val testName = file.getName
          solverToWriter(prefix+solverType.toString).write(s"$testName $result\n")
        })
      })
    }
    closeOutputFiles(solverToWriter)
  }

}
