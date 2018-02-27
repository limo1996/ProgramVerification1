package util

import smtlib.parser.Commands.{Assert, CheckSat, GetModel, _}
import smtlib.parser.Terms.{Identifier, SimpleIdentifier, Term}
import smtlib.theories.Core.BoolSort
import core.MySATSolver.abortExecution

object InputProcessing {

  // this method checks that the initial commands are the standard ones, and then extracts the declared variable identifiers and input formula to check for satisfiability
  def processCommands(inputCommands : List[Command]) : (List[Identifier],Term) = {

    // "var" indicates a mutable variable; we are free to mix functional / imperative -style code in Scala
    var script: List[Command] = inputCommands

    // Scala supports pattern-matching, using "value match {...}" syntax, where the {...} is a (possibly partial) function defined by cases, defining the pattern-match possibilities
    // Scala List collections work like functional language lists (e.g. as in Haskell)
    // any empty list is written List()
    // a "cons" is written x :: xs
    script match {
      case SetOption(ProduceModels(true)) :: cmds => // this is the first command we expect in the input: (set-option :produce-models true)
        // whitespace is not generally significant in Scala
        script = cmds // drop the first line imperative-style; via mutation

      // pattern cases are tried in order, as in Haskell
      case cmd :: cmds => abortExecution("Unexpected first command: " + cmd.toString) // note: + performs String append
      case List() => abortExecution("Empty list of SMTlib commands found.")
    }

    // This time, let's drop the line functional-style, using the value returned from a pattern-match:
    val bodyCommands : List[Command] = script match {
      case SetLogic(_) :: cmds =>
        // the "_" in the pattern-match means any value can occur in this position
        // alternatively, we could match on the type (not on the object structure) and use "case _: SetLogic"; this means that we expect an object of type SetLogic, but we won't give that object a name (hence the "_")
        cmds
      case cmd :: cmds => abortExecution(s"Expected (set-logic QF_UF) command as second command, but found: $cmd") // note: the "toString" call on cmd can be omitted; if a String is expected, and a reference with a toString method is provided, the call will be inserted automatically
      case List() => abortExecution("Found only a single SMTlib command, but expected several.")
    }

    // Scala supports first-class functions (closures); here, we define the a function which checks whether a given command is an instance of DeclareFun (_.isInstanceOf[T] is the general form for type-testing in Scala)
    val declarationFilter : Command => Boolean = // function type
          c => c.isInstanceOf[DeclareFun] // here, c is the function parameter (you could think of this as lambda c. c.isInstanceOf[DeclareFun])

    // We could also declare above function as follows (the omitted return type will be inferred):
    //   val declarationFilter = (c: Command) => c.isInstanceOf[DeclareFun]

    // we can declare and assign pairs / tuples in Scala, rather than declaring each element separately
    val (declarationCommands, remainingCommands) = (bodyCommands.takeWhile(declarationFilter), bodyCommands.dropWhile(declarationFilter)) // actually, Scala has a library method "span" for this takeWhile/dropWhile combination:  see http://www.scala-lang.org/api/2.12.1/scala/collection/immutable/List.html

    if(declarationCommands.isEmpty) {
      abortExecution("No declaration commands found.")
    }
    // cast all of the declarations to the DeclareFun type
    val declarations : List[DeclareFun] = declarationCommands.map(c => c.asInstanceOf[DeclareFun]) // _.asInstanceOf[T] is a type-cast expression in Scala (generates a runtime error if the value it is applied to cannot be cast to type T

    // check that we do not have a declaration in our list for a function which takes parameters, or which doesn't have the Bool sort
    declarations.find(d => // "find" takes a function mapping a value to Boolean, and returns an Option type (see http://www.scala-lang.org/api/2.12.x/scala/Option.html ) - which works like the Maybe type in Haskell
      d.paramSorts.nonEmpty || d.returnSort != BoolSort()
    ) match {
      case Some(d) =>
        // Using string interpolation (s"... $d ...") often results in more readable code, but not always.
        // In the following, we use simple string concatenation instead.
        abortExecution("Found a declaration which doesn't appear to be a propositional variable: " + d + d.paramSorts + d.returnSort)
      case None => // this is what we expect - there is no such declaration!
    }

    val variables : List[Identifier] = declarations.map(d => SimpleIdentifier(d.name))
    // SimpleIdentifier(s) is essentially a synonym for Identifier(s,Seq()); Identifier objects take an optional second parameter which is a sequence, but we can always leave it empty for our purposes.

    remainingCommands match {
      case Assert(f) :: CheckSat() :: GetModel() :: List() => // this is the format we expect
        (variables,f) // this is the value we return from the entire method, since this is the last statement executed in the method body
      case Assert(f) :: CheckSat() :: List() =>
        (variables,f)
      case _ => abortExecution("Failed to parse the expected postfix commands (assert, check-sat, get-model); found: " + remainingCommands) // remainingCommands is still accessible inside the pattern-match cases
    }
  }
}
