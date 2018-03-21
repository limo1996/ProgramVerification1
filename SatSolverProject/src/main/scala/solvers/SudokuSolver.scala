package solvers

import scala.collection.mutable
import scala.io.Source
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.StringBuilder

import core.MySATSolver
import smtlib.parser.Commands.Command
import smtlib.parser.Terms.{QualifiedIdentifier, SimpleIdentifier, Term}
import smtlib.theories.Core._

/**
  * Based on https://pdfs.semanticscholar.org/3d74/f5201b30772620015b8e13f4da68ea559dfe.pdf
  * @param CDCL Indicates whether use CDCL solver
  * @param pureLiteralRule Indicates whether to use pure literal rule
  */
class SudokuSolver(val CDCL : Boolean, val pureLiteralRule : Boolean) {
  val _builder = new mutable.StringBuilder()

  def solve(path: String) : Unit = {
    val sudoku = parseFile(path)
    createSudokuFormulaString(sudoku)

  }

  private def parseFile(path: String) : ArrayBuffer[Array[Int]] = {
    val sudoku: ArrayBuffer[Array[Int]] = ArrayBuffer[Array[Int]]()
    for (line <- Source.fromFile(path).getLines) {
      sudoku.append(line.map(c => c.toString.toInt).toArray)
    }
    assert (sudoku.size == 9)
    sudoku
  }

  private def smt2StringToFormula(inputString: String): Term = {
    val cmds: List[Command] = MySATSolver.parseInputString(inputString)
    val (_, formula) = util.InputProcessing.processCommands(cmds)
    formula
  }

  private def varName(row: Int, column: Int, number: Int) : String = {
    val sb = new StringBuilder(4)
    sb.append("v")
    sb.append(row)
    sb.append(column)
    sb.append(number)
    return sb.result()
  }

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
  private def appendVar(row: Int, column: Int, number: Int) : Unit = {
    _builder.append(f" ${varName(row, column, number)}")
  }
  private def appendPreamble() : Unit = {
    _builder.append("\"(set-option :produce-models true)\n (set-logic QF_UF)\n")
  }
  private def appendVarDecl(row: Int, column: Int, number: Int) : Unit = {
    _builder.append("(declare-fun " + varName(row, column, number) + "() Bool)\n");
  }

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

    _builder.append("(assert\n")
    // force variables representing input number to be true
    for(i <- 0 to 8){
      for(j <- 0 to 8){
        if(sudoku(i)(j) != 0) {
          appendVar(i, j, sudoku(i)(j))
        }
      }
    }

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
      }
      appendEnd()
    }
    appendEnd()

    // Each number appears at most once in each row:
    appendAnd()
    for(column <- 1 to 9){
      appendAnd()
      for(number <- 1 to 9){
        appendAnd()
        for(row <- 1 to 8){
          //if(row + 1 != 9) {
            appendAnd()
            for (i <- row + 1 to 9) {
              appendOr()
              appendNot(); appendVar(row, column, number); appendEnd()
              appendNot(); appendVar(i, column, number); appendEnd()
              appendEnd()
            }
            appendEnd()
          //}
        }
        appendEnd()
      }
      appendEnd()
    }
    appendEnd()

    // Each number appears at most once in each column:
    appendAnd()
    for(row <- 1 to 9){
      appendAnd()
      for(number <- 1 to 9){
        appendAnd()
        for(column <- 1 to 8){
          //if(column + 1 != 9) {
            appendAnd()
            for(i <- column + 1 to 9){
              appendOr()
              appendNot(); appendVar(row, column, number); appendEnd()
              appendNot(); appendVar(column, i, number); appendEnd()
              appendEnd()
            }
            appendEnd()
          //}
        }
        appendEnd()
      }
      appendEnd()
    }
    appendEnd()

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
              appendAnd()
              for(k <- y + 1 to 3){
                appendOr()
                appendNot(); appendVar(3*i + x, 3*j + y, z); appendEnd()
                appendNot(); appendVar(3*i + x, 3*j + k, z); appendEnd()
                appendEnd()
              }
              appendEnd()
            }
            appendEnd()
          }
          appendEnd()
        }
        appendEnd()
      }
      appendEnd()
    }
    appendEnd()

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
                }
                appendEnd()
              }
            }
            appendEnd()
          }
          appendEnd()
        }
        appendEnd()
      }
      appendEnd()
    }
    appendEnd()

    _builder.append("\n)\n")
    _builder.append("(check-sat)\n(get-model)\n")

  }

}
