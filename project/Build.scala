import sbt._
import Keys._
import com.typesafe.sbt.SbtStartScript
import SbtStartScript.StartScriptKeys._

object MRSCBuild extends Build {

  override lazy val settings = super.settings ++ Seq(scalaVersion := "2.10.1")

  lazy val MRSCProject = Project("mrsc", file("src/mrsc"),
    settings = Project.defaultSettings ++ 
    SbtStartScript.startScriptForClassesSettings ++
    Seq(
      organization := "mrsc",
      name := "mrsc",
      version := "0.5",
      mainClass in Compile := Some("mrsc.frontend.CLI"),
      libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.0.0",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      libraryDependencies += "org.rogach" %% "scallop" % "0.9.2",
      libraryDependencies += "com.twitter" %% "util-eval" % "6.3.6",
      startScriptName <<= target / "mrsc-cli",
      unmanagedBase := file("lib"),
      fork := true,
      baseDirectory in run := file("."),
      testOptions in Test += Tests.Argument("-oD")
    )
  )

  lazy val SamplesProject = Project("samples", file("src/samples"),
    settings = Project.defaultSettings ++ Seq(
      libraryDependencies += "org.scalaz" %% "scalaz-core" % "6.0.4",
      fork := true,
      baseDirectory in run := file(".")
    )
  ) dependsOn(MRSCProject)

  lazy val ArraysProject = Project("arrays", file("src/arrays"),
    settings = Project.defaultSettings ++ Seq(
      libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.0.0",
      fork := true,
      baseDirectory in run := file(".")
    )
  ) dependsOn(MRSCProject)

  lazy val root = Project(id = "parent", base = file(".")) aggregate(MRSCProject, SamplesProject, ArraysProject)
}
