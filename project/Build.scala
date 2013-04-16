import sbt._
import Keys._

object MRSCBuild extends Build {

  override lazy val settings = super.settings ++ Seq(scalaVersion := "2.10.1")

  lazy val MRSCProject = Project("mrsc", file("src/mrsc"),
    settings = Project.defaultSettings ++ Seq(
      libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.0.0-RC2",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      libraryDependencies += "junit" % "junit" % "4.8.1" % "test",
      unmanagedBase := file("lib"),
      fork := true,
      baseDirectory in run := file(".")
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
      libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.0.0-RC2",
      fork := true,
      baseDirectory in run := file(".")
    )
  ) dependsOn(MRSCProject)

  lazy val root = Project(id = "parent", base = file(".")) aggregate(MRSCProject, SamplesProject, ArraysProject)
}
