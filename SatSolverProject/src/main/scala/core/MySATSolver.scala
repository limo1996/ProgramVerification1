package core

import CNF2SMTLIB.CNF2SMTLIBv2Converter
import smtlib.parser.Commands._
import solvers.SolverFactory
import util.PropositionalLogic

sealed trait InputFormat {}

case object SMTLib extends InputFormat {}
case object DIMACS extends InputFormat {}

/**
  * A class for parsing command line arguments.
  *
  * The current expected format of the command line arguments is:
  *
  *   run <configuration-name> <test-file> [--cnf]
  *
  * The argument <configuration-name> is parsed by the method
  * SolverFactory.getConfigurationFromString.
  *
  * You can change the command-line format expected, as long as you document this in your report.
  */
private class Settings(args: Array[String]) {

  import MySATSolver.abortExecution

  if(args.length != 2 && args.length != 3) {
    abortExecution("Wrong number of command-line arguments specified (expected 2 or 3)")
  }

  val implementation: solvers.SATSolverConfiguration =
    SolverFactory.getConfigurationFromString(args(0)).getOrElse(
      abortExecution(s"Unknown algorithm: ${args(0)}")
    )

  val file: String = args(1)

  val inputFormat: InputFormat = {
    if (args.length == 3) {
      args(2) match {
        case "--cnf" | "/cnf" | "--dimacs" | "/dimacs" => DIMACS
        case "--smtlib" | "/smtlib" => SMTLib
        case s => abortExecution(s"Unknown input format: $s")
      }
    } else {
      SMTLib
    }
  }

}

// A Scala "object" is a singleton object. Here, we merely use it to hold, in the Java-sense,
// static methods, by declaring them inside the object.
object MySATSolver {

  // This is a Scala method declaration: it declares a method with a single argument and no
  // return value (void in Java)
  def main(args: Array[String]) {
    // check that a command-line argument was passed (which will be treated as the input String)

    val settings = new Settings(args)

    // "val" indicates immutable storage; we will never reassign inputString
    val inputString = // we can use a block of statements as an expression; its value will be
                      // the value of the last statement in the block
    {
      settings.inputFormat match {
        case SMTLib =>
          // This pattern is typical for reading an entire text file into a String
          val source = scala.io.Source.fromFile(args(1))
          try source.mkString finally source.close() // make sure the file is closed
        case DIMACS =>
          // convert from .cnf (DIMACS) format
          convertDIMACSFileToSMTLIBv2(args(1))
      }
    }

    // type annotations on declarations (such as "List[Command]" here) are optional; the compiler
    // will otherwise try to infer a type from the assigned right-hand-side expression
    // However, it might not always choose the type you expect, and sometimes adding the types
    // explicitly can make code more readable.
    val script: List[Command] = parseInputString(inputString)

    // we can declare and assign pairs / tuples in Scala, rather than declaring each element separately
    val (declarations, formula) = util.InputProcessing.processCommands(script)
                      // extract the list of identifiers and input formula from the list of smtlib commands

    // Now, we have the list of function declarations (corresponding to the variables in the input
    // problem), and the formula to check for satisfiability

    // A runtime check: if the first parameter isn't true, the execution aborts with the (optional)
    // second parameter as the exception message
    // The message is formatted using string interpolation (requires strings of the shape s"...").
    // To splice the result of a more complex Scala expression into a string, surround it with curly
    // braces, e.g. s"1 > ${1 + 1}".
    assert(PropositionalLogic.isPropositional(formula),
           s"The parsed formula is not a propositional formula; got: $formula")

    // might be useful for initial debugging:
    println("Declarations: \n" + declarations)
    println("Input Formula: " + formula)

    // e.g. (if you implemented a DP SAT Solver as a DPSolver class):
    val solver: SATSolver = SolverFactory.constructSolver(settings.implementation)
    val result = solver.checkSAT(formula)
    result match {
      case Some(model) =>
        assert(PropositionalLogic.evaluate(formula, model))
        println("Successfully evaluated model.")
      case None =>
    }
    println(solver.outputResult(result))
  }

  // A Scala method that, unlike method main above, has a return value
  def parseInputString(input : String) : List[Command] = {
    // make use of the pre-existing smtlib Lexer and Parser
    val lexer = new smtlib.lexer.Lexer(new java.io.StringReader(input)) // Java libraries and code can be used interchangeably in Scala code
    val parser = new smtlib.parser.Parser(lexer)

    // Scala has both immutable and mutable collection libraries. Here a mutable one makes more sense (since we build it up incrementally), but either could be used.
    // Typically, a mutable collection is used with an immutable local variable (val), whereas an immutable collection is used with a mutable local variable (var).
    val cmds = new scala.collection.mutable.ListBuffer[Command]
    var cmd = parser.parseCommand // try to parse the next command in the input SMTlib string
    while(cmd != null) { // keep parsing all of the commands into a list of smtlib.parser.Commands.Command instances
      cmds.append(cmd)
      cmd = parser.parseCommand
    }

    cmds.toList // In Scala, the value of the last statement in a block is the value of the block (here, the return value of the parseScript method)
  }

  // Used to abort execution of the program - we could alternatively use exceptions (which work exactly as in Java) for this
  def abortExecution(reason: String) : Nothing = { // Nothing is a type that no value will ever have; a method returning "Nothing" is guaranteed not to return normally (in this case, because it exits). "Nothing" is a subtype of all types, allowing calls to this method to type-check in any position.
    println(reason) // print or println are useful for debugging, too
    println("Usage: MySatSolver <algorithm> <file> [--cnf]")
    println(s"Supported algorithms: ${SolverFactory.getAllSupportedSolvers.mkString(", ")}")
    sys.exit(1) // abort the program with exit code 1
  }

  // Helper method for converting SAT input files into SMT-LIB format.
  // You probably won't need this method, at least initially.
  // This method will (only) be useful if you want to test your implementation against SAT benchmarks that you find online (these are typically in DIMACS format, rather than SMTlib)
  def convertDIMACSFileToSMTLIBv2(fileInDIMACSFormat : String) : String = {
    val converter = new CNF2SMTLIBv2Converter // parentheses are generally not needed for calls which take no parameters
    converter.convertDimacs(fileInDIMACSFormat)
  }
}
