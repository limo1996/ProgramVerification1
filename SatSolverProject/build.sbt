name := "SatSolverProject"

version := "1.0"

autoScalaLibrary := true

scalaVersion := "2.12.4"

resolvers += "OSS Sonatype" at "https://repo1.maven.org/maven2/"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.13.4" % "test"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.4"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.4" % "test"

testOptions in Test += Tests.Argument(TestFrameworks.ScalaCheck, "-verbosity", "2")

fork in Test := true

lazy val scalasmtlib = RootProject(file("../scala-smtlib"))
val main = Project(id = "SatSolverProject", base = file(".")).dependsOn(scalasmtlib) 