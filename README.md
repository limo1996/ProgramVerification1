# Program Verification: Project 1

[![build status](/../badges/master/build.svg)](/../commits/master)

Structure of the repository:

+   `SatSolverProject` – the directory that contains the initial files
    of the project.
+   `scala-smtlib` – the directory that contains the library for parsing
    input files in the SMTLIB format.
+   `docker` – the definition of the Docker image used by the GitLab
    build. It is provided for those who would like to reproduce the
    build environment on their computers. You can safely ignore this
    folder.

Quick start (assuming you have SBT installed):

1.  Run all tests:

    ```
    cd SatSolverProject
    sbt
    test
    ```

2.  Run a specific configuration of your solver on a `smt2` file:

    ```
    cd SatSolverProject
    sbt
    run DPLLBaseline src/test/resources/test.smt2
    ```

    Here, `DPLLBaseline` is the configuration name that is parsed by
    the `SolverFactory.getConfigurationFromString` method.

3.  Run a specific configuration of your solver on a `cnf` file:

    ```
    cd SatSolverProject
    sbt
    run DPLLBaseline src/test/resources/test.cnf --cnf
    ```
