package solvers

import scala.collection.mutable
import scala.io.Source
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.StringBuilder

import core.MySATSolver
import core.SATSolver
import core.CNFConversion


import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets

import smtlib.parser.Commands.Command
import smtlib.parser.Terms.{QualifiedIdentifier, SimpleIdentifier, Term}
import smtlib.theories.Core._

/**
  * To run sudoku tap a command:
  * run CDCLBaseline /Users/limo/Documents/eth-courses/ProgramVerification/Projects/Project1/SatSolverProject/src/test/resources/sudoku/medium.txt --sudoku
  * where second argument is path to file.
  * Afterwards you should see solution in the same folder with .res appended after file name
  */

/**
  * Based on https://pdfs.semanticscholar.org/3d74/f5201b30772620015b8e13f4da68ea559dfe.pdf
  * @param CDCL Indicates whether use CDCL solver
  * @param pureLiteralRule Indicates whether to use pure literal rule
  */
class SudokuSolver(val CDCL : Boolean, val pureLiteralRule : Boolean) {
  val _builder = new mutable.StringBuilder()

  /* Solves sudoku problem specified in file provided as parameter. */
  def solve(path: String) : Unit = {
    val sudoku = parseFile(path)
    println("Sudoku: file parsed")
    createSudokuFormulaString(sudoku)
    Files.write(Paths.get(path+".result"), _builder.toString.getBytes(StandardCharsets.UTF_8))
    println("Sudoku: formula string created")
    val solver = getSolver(CDCL, pureLiteralRule)
    println("Sudoku: Solver create. Formula is going to be solved")
    val formula = smt2ToFormula(_builder.toString())
    //val cnf = CNFConversion.toCNF(formula)
    val result = solver.checkSAT(formula)
    println("Sudoku: formula solved")
    writeResultToFile(result, path)
  }

  /* Gets solver from specification provided as parameter. */
  private def getSolver(CDCL : Boolean, pureLiteralRule : Boolean) : SATSolver = {
    if(CDCL)
      new CDCL(pureLiteralRule)
    else
      new DPLL(pureLiteralRule)
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

  /* Converts input string into smt2lib formula */
  private def smt2ToFormula(inputString: String): Term = {
    val cmds: List[Command] = MySATSolver.parseInputString(inputString)
    val (_, formula) = util.InputProcessing.processCommands(cmds)
    println(formula)
    formula
  }

  /* gets name of variable specified by row, column and number it represents. */
  private def varName(row: Int, column: Int, number: Int) : String = {
    val sb = new StringBuilder(4)
    sb.append("v")
    sb.append(row)
    sb.append(column)
    sb.append(number)
    return sb.result()
  }

  /**
    * Helper functions for appending to String Builder
    */

  private def appendAnd() : Unit = {
    _builder.append("(and ");
  }
  private def appendOr() : Unit = {
    _builder.append("(or ")
  }
  private def appendNot() : Unit = {
    _builder.append("(not ")
  }
  private def appendEnd() : Unit = {
    _builder.append(")")
  }
  private def appendNL() : Unit = {
    _builder.append("\n")
  }
  private def appendVar(row: Int, column: Int, number: Int) : Unit = {
    _builder.append(f" ${varName(row, column, number)}")
  }
  private def appendPreamble() : Unit = {
    _builder.append("(set-option :produce-models true)\n (set-logic QF_UF)\n")
  }
  private def appendVarDecl(row: Int, column: Int, number: Int) : Unit = {
    _builder.append("(declare-fun " + varName(row, column, number) + "() Bool)\n");
  }

  /* Creates smt2 string from provided sudoku. */
  private def createSudokuFormulaString(sudoku: ArrayBuffer[Array[Int]]) : Unit = {
    // first goes smt preamble
    appendPreamble()

    // append variable declarations
    for(row <- 1 to 9){
      for(column <- 1 to 9){
        for(number <- 1 to 9){
          appendVarDecl(row, column, number)
        }
      }
    }

    appendNL()
    _builder.append("(assert\n")
    appendAnd()
    // force variables representing input number to be true
    for(i <- 0 to 8){
      for(j <- 0 to 8){
        if(sudoku(i)(j) != 0) {
          appendVar(i + 1, j + 1, sudoku(i)(j))
        }
      }
    }
    appendNL()

    // There is at least one number in each entry:
    appendAnd()
    for(row <- 1 to 9){
      appendAnd()
      for(column <- 1 to 9){
        appendOr()
        for(number <- 1 to 9){
          appendVar(row, column, number)
        }
        appendEnd()
        appendNL()
      }
      appendEnd()
      appendNL()
    }
    appendEnd()
    appendNL()

    // Each number appears at most once in each row:
    appendAnd()
    for(column <- 1 to 9){
      appendAnd()
      for(number <- 1 to 9){
        appendAnd()
        for(row <- 1 to 9){
          if(row + 1 <= 9) {
            appendAnd()
            for (i <- row + 1 to 9) {
              appendOr()
              appendNot(); appendVar(row, column, number); appendEnd()
              appendNot(); appendVar(i, column, number); appendEnd()
              appendEnd()
            }
            appendEnd()
            appendNL()
          }
        }
        appendEnd()
        appendNL()
      }
      appendEnd()
      appendNL()
    }
    appendEnd()
    appendNL()

    // Each number appears at most once in each column:
    appendAnd()
    for(row <- 1 to 9){
      appendAnd()
      for(number <- 1 to 9){
        appendAnd()
        for(column <- 1 to 9){
          if(column + 1 <= 9) {
            appendAnd()
            for(i <- column + 1 to 9){
              appendOr()
              appendNot(); appendVar(row, column, number); appendEnd()
              appendNot(); appendVar(row, i, number); appendEnd()
              appendEnd()
            }
            appendEnd()
            appendNL()
          }
        }
        appendEnd()
        appendNL()
      }
      appendEnd()
      appendNL()
    }
    appendEnd()
    appendNL()

    // Each number appears at most once in each 3x3 sub-grid
    appendAnd()
    for(z <- 1 to 9){
      appendAnd()
      for(i <- 0 to 2){
        appendAnd()
        for(j <- 0 to 2){
          appendAnd()
          for(x <- 1 to 3){
            appendAnd()
            for(y <- 1 to 3){
              if (y + 1 <= 3) {
                appendAnd()
                for (k <- y + 1 to 3) {
                  appendOr()
                  appendNot(); appendVar(3 * i + x, 3 * j + y, z); appendEnd()
                  appendNot(); appendVar(3 * i + x, 3 * j + k, z); appendEnd()
                  appendEnd()
                }
                appendEnd()
                appendNL()
              }
            }
            appendEnd()
            appendNL()
          }
          appendEnd()
          appendNL()
        }
        appendEnd()
        appendNL()
      }
      appendEnd()
      appendNL()
    }
    appendEnd()
    appendNL()

    // Each number appears at most once in each 3x3 sub-grid
    appendAnd()
    for(z <- 1 to 9){
      appendAnd()
      for(i <- 0 to 2){
        appendAnd()
        for(j <- 0 to 2){
          appendAnd()
          for(x <- 1 to 3){
            if (x + 1 <= 3) {
              appendAnd()
              for (y <- 1 to 3) {
                appendAnd()
                for (k <- x + 1 to 3) {
                  appendAnd()
                  for (l <- 1 to 3) {
                    appendOr()
                    appendNot(); appendVar(3 * i + x, 3 * j + y, z); appendEnd()
                    appendNot(); appendVar(3 * i + k, 3 * j + l, z); appendEnd()
                    appendEnd()
                  }
                  appendEnd()
                  appendNL()
                }
                appendEnd()
                appendNL()
              }
              appendEnd()
              appendNL()
            }
          }
          appendEnd()
          appendNL()
        }
        appendEnd()
        appendNL()
      }
      appendEnd()
      appendNL()
    }
    appendEnd()
    appendNL()

    // append and of assertion
    appendEnd()
    _builder.append("\n)\n")
    // specify we want to solve formula and get model
    _builder.append("(check-sat)\n(get-model)\n")
  }

  /* Writes 9x9 result marix into file with extension .res */
  private def writeResultToFile(res: Option[Map[String,Boolean]], originalPath: String) : Unit = {
    assert(res.isDefined)
    val formula = res.get
    val newPath : String = originalPath + ".res";
    val sudoku = parseResult(formula)
    val builder = new StringBuffer()
    for(row <- sudoku){
      for(entry <- row){
        builder.append(entry)
      }
      builder.append('\n')
    }
    Files.write(Paths.get(newPath), builder.toString.getBytes(StandardCharsets.UTF_8))
  }

  /* Converts final assignment of variables into resulting 9x9 matrix */
  private def parseResult(res: Map[String, Boolean]) : Array[Array[Int]] = {
    val sudoku = Array.fill(9){Array.fill(9){0}}
    for ((k: String, v: Boolean) <- res){
      if(v){
        //println(k)
        val x = k.charAt(1).toInt - 48
        val y = k.charAt(2).toInt - 48
        val value = k.charAt(3).toInt - 48
        //println("x: " + x + " y: " + y)
        sudoku(x - 1)(y - 1) = value
      }
    }
    sudoku
  }

}
