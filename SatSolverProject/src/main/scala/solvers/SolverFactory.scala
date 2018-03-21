package solvers

import core.SATSolver

sealed trait SATSolverConfiguration {}

// TODO: Extend with different configurations.

case object Z3 extends SATSolverConfiguration {}
case object DPLLBaseline extends SATSolverConfiguration {}
case object DPLLWithoutPure extends SATSolverConfiguration {}
case object CDCLBaseline extends SATSolverConfiguration {}
case object FixedProblemSolver extends SATSolverConfiguration {}

/**
  * Factory for constructing SAT solvers.
  */
object SolverFactory {

  /**
    * Converts the command line argument into the solver configuration.
    * You can find more about command line argument parsing in the
    * documentation string of the core.Settings class.
    *
    * @param name The command line argument that contains the configuration name.
    */
  def getConfigurationFromString(name: String): Option[SATSolverConfiguration] = name match {
    // TODO: Extend with different configurations.
    case "Z3" => Some(solvers.Z3)
    case "FixedProblemSolver" => Some(solvers.FixedProblemSolver)
    case "DPLLBaseline" => Some(solvers.DPLLBaseline)
    case "DPLLWithoutPure" => Some(solvers.DPLLWithoutPure)
    case "CDCLBaseline" => Some(solvers.CDCLBaseline)
    case _ => None
  }

  def getAllSupportedSolvers: Seq[SATSolverConfiguration] = {
    // TODO: Add all your solver configurations to this list so that they can be automatically tested.
    List(
//      solvers.DPLLBaseline,
      solvers.DPLLWithoutPure,
      solvers.CDCLBaseline
    )
  }

  /**
    * This method is responsible for building SAT solvers of a specific configuration.
    */
  def constructSolver(solverConfiguration: SATSolverConfiguration): SATSolver = solverConfiguration match {
    case solvers.Z3 => Z3Solver
    case solvers.FixedProblemSolver => FixedProblemSATSolver
    case solvers.DPLLBaseline => new DPLL(usePureLiteralRule = true)
    case solvers.DPLLWithoutPure => new DPLL(usePureLiteralRule = false)
    case solvers.CDCLBaseline => new CDCL(usePureLiteralRule = false)
  }

}
