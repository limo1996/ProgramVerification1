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

object Evaluator {
  private val runs = 15                         // # experiments for every configuration
  private val dropRuns = 5                      // # of experiments to be ignored
  private val timeout = Duration(10, SECONDS)   // max duration in which an experiment should terminate

  private val outputDirPath = "results/"
  private val outputFileExtension = ".time"
  private val dirPathsToPrefixes = Map("examples" -> "Examples_",
    "tests/random" -> "Random_", "tests/structured" -> "Structured_")
  private var solverToWriter = Map[String, BufferedWriter]()

  /**
    * Creates and runs evaluation experiments for every solver and every test file.
    */
  def run(): Unit = {
    createOutputFiles()

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

    closeOutputFiles()
  }

  /**
    * @param solver - Solver used for the experiments.
    * @param formula - Formula that is checked @runs times.
    * @return - "timeout" if an experiment timeouts, else the average execution time
    *         of the last (@runs - @dropRuns) experiments.
    */
  private def averagedExperiment(solver: SATSolver, formula: Term): String = {
    var results = Seq[Double]()                                 // stores the experiments' timings

    // Run experiment @runs times.
    for (ith_run <- 1 to runs) {
      val result = runExperiment(solver, formula)

      // Consider only experiments after the first @dropRuns (warm up time)
      if (ith_run > dropRuns) {
        result match {
          case -1 => return "timeout"
          case _ => results = result +: results
        }
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
    try {
      Await.result(Future[Double] {
        val start = System.currentTimeMillis()
        solver.checkSAT(formula)
        val end = System.currentTimeMillis()
        end - start
      }, timeout)
    } catch {
      case _: Exception => -1  // catch whatever exception the interrupt solver may throw
    }
  }


  /**
    * Creates a file for every available solver and populates the @solverToWriter map
    * with a writer for this file.
    */
  private def createOutputFiles(): Unit = {
    dirPathsToPrefixes.foreach{ case(_, prefix) =>
      SolverFactory.getAllSupportedSolvers.foreach((solverType) => {
        val file = new File(outputDirPath + prefix + solverType.toString + outputFileExtension)
        val bw = new BufferedWriter(new FileWriter(file))
        solverToWriter += (prefix+solverType.toString -> bw)
      })
    }
  }

  private def closeOutputFiles(): Unit = {
    for ((_, writer) <- solverToWriter) {
      writer.close()
    }
  }

  private def collectFiles(path: String, extension: String) = {
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
