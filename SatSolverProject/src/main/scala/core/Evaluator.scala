package core

import java.io.{BufferedWriter, File, FileWriter}

import CNF2SMTLIB.CNF2SMTLIBv2Converter
import smtlib.parser.Commands.Command
import smtlib.parser.Terms.Term
import solvers.SolverFactory

import scala.collection.mutable
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global

class Evaluator {
  protected val runs = 15                         // # experiments for every configuration
  protected val dropRuns = 5                      // # of experiments to be ignored
  protected val timeout = 10000                   // max duration in which an experiment should terminate

  private val outputDirPath = "../results/"
  private val outputFileExtension = ".time"

  /**
    * Creates and runs evaluation experiments for every solver and every test file.
    */
  def run(): Unit = {
    val dirPathsToPrefixes = Map("examples" -> "Examples_", "sudoku" -> "Sudoku_",
      "benchmark_formulas/random" -> "Random_", "benchmark_formulas/structured" -> "Structured_")
    val solverToWriter = createOutputFiles(dirPathsToPrefixes)

    dirPathsToPrefixes.foreach{ case(dirPath, prefix) =>
      val files = collectFiles(dirPath, ".cnf") ++ collectFiles(dirPath, ".smt2")
      files foreach ((file) => {
        println(file.toString)
        var inputString: String = null

        // Handle *.cnf and *.smt2 files accordingly.
        if (file.getName.endsWith(".cnf")) {
          val converter = new CNF2SMTLIBv2Converter
          inputString = converter.convertDimacs(file.getAbsolutePath)
        } else {
          inputString = {
            val source = scala.io.Source.fromFile(file)
            try source.mkString finally source.close()
          }
        }

        val script: List[Command] = MySATSolver.parseInputString(inputString)
        val (_, formula) = util.InputProcessing.processCommands(script)

        // Check formula under every solver and log results.
        SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
          val solver = SolverFactory.constructSolver(solverType)
          val result = averagedExperiment(solver, formula)
          val literalCount = solver.convertToCNF(formula).literalCount

          // Log the number of literals in the formula and the average time it took to solve
          if (prefix == "Random_") {
            solverToWriter(prefix+solverType.toString).write(s"$literalCount $result\n")
          } else {
            val testName = file.getName
            solverToWriter(prefix+solverType.toString).write(s"$testName $result\n")
          }
        })
      })
    }
    closeOutputFiles(solverToWriter)
  }

  /**
    * @param solver - Solver used for the experiments.
    * @param formula - Formula that is checked @runs times.
    * @return - "timeout" if an experiment timeouts, else the average execution time
    *         of the last (@runs - @dropRuns) experiments.
    */
  protected def averagedExperiment(solver: SATSolver, formula: Term): String = {
    var results = Seq[Double]()                                 // stores the experiments' timings

    // Run experiment @runs times.
    for (ith_run <- 1 to runs) {
      val result = runExperiment(solver, formula)

      // Consider only experiments after the first @dropRuns (warm up time)
      if (ith_run > dropRuns) {
        if (result > timeout) return "timeout"
        else results = result +: results
      }
    }

    (results.sum / results.size).toString
  }

  /**
    * @param solver - Solver used for the experiment.
    * @param formula - Formula that is checked.
    * @return - -1 if experiment timeouts, else the duration of the experiment in milliseconds.
    */
  private def runExperiment(solver: SATSolver, formula: Term): Double = {
    val start = System.currentTimeMillis()
    solver.checkSAT(formula)
    val end = System.currentTimeMillis()
    end - start
  }


  /**
    * Creates a file for every available solver and populates the @solverToWriter map
    * with a writer for this file.
    */
  protected def createOutputFiles(dirPathsToPrefixes: Map[String, String]): Map[String, BufferedWriter] = {
    var solverToWriter = Map[String, BufferedWriter]()
    dirPathsToPrefixes.foreach{ case(_, prefix) =>
      SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
        val file = new File(outputDirPath + prefix + solverType.toString + outputFileExtension)
        val bw = new BufferedWriter(new FileWriter(file))
        solverToWriter += (prefix+solverType.toString -> bw)
      })
    }
    solverToWriter
  }

  protected def closeOutputFiles(solverToWriter: Map[String, BufferedWriter]): Unit = {
    for ((_, writer) <- solverToWriter) {
      writer.close()
    }
  }

  protected def collectFiles(path: String, extension: String) : mutable.Buffer[File] = {
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

    collectFiles(new File("src/test/resources/" + path))
    paths
  }
}
