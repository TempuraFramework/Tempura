ThisBuild / version := "0.1.0"

ThisBuild / scalaVersion := "3.7.3"

libraryDependencies ++= Seq(
  "org.scalacheck" %% "scalacheck" % "1.15.4" % "test",
  "org.scalatestplus" %% "scalacheck-1-18" % "3.2.19.0" % "test",
  "org.scalatest" %% "scalatest" % "3.2.19",
  "org.typelevel" %% "cats-parse" % "1.0.0",
  "org.typelevel" %% "cats-core" % "2.13.0",
  "org.typelevel" %% "cats-laws" % "2.13.0",
  "org.typelevel" %% "algebra" % "2.13.0",
  "org.typelevel" %% "cats-kernel" % "2.13.0",
  "org.typelevel" %% "cats-free" % "2.13.0",
  "org.typelevel" %% "cats-testkit" % "2.13.0",
  "org.typelevel" %% "shapeless3-deriving" % "3.4.0",
  "org.typelevel" %% "shapeless3-typeable" % "3.4.0",
  "com.lihaoyi" % "ammonite_3.6.3" % "3.0.2", //% "test" cross CrossVersion.full,
  "de.uni-freiburg.informatik.ultimate" % "smtinterpol" % "2.5-1388-ga5a4ab0c", // SMTInterpol
  //"tools.aqua" % "z3-turnkey" % "4.14.1" ,// Z3-Turnkey: https://github.com/tudo-aqua/z3-turnkey
  "tools.aqua" % "cvc5-turnkey" % "1.2.0" // CVC5-Turnkey: https://github.com/tudo-aqua/cvc5-turnkey
)

// TODO: Ammonite cannot accept stdin if we set run / fork := true.
// TODO we might try `ThisBuild / run / connectInput := true` next.

////////////////

// Detect platform -> choose native dir -> set the right env var (PATH/LD_/DYLD_)
val os   = sys.props.getOrElse("os.name", "").toLowerCase
val arch = sys.props.getOrElse("os.arch", "").toLowerCase

val platform =
  if (os.contains("mac")) // TODO: we don't have binaries for amd64 yet.
    if (arch.contains("64") "macos-x86_64" else "macos-arm64"
  else "linux-x86_64"

lazy val pPrint = settingKey[Unit]("example")

pPrint := {
  println("\n******* Platform: " + platform + " ****** \n")
  println("\n  LD_LIBRARY_PATH: " + (baseDirectory.value / "lib" / platform).getAbsolutePath + "\n")
  println("\n  DYLD_LIBRARY_PATH: " +  (baseDirectory.value / "lib" /  platform).getAbsolutePath + "\n")
  println("\n***************************************** \n")
}

// CAUTION: To override java.library.path we need to run in fork := true mode.
// But by default in this mode Ammonite console will break, so we also need
// to pipe in stdin via setting connectInput := true.
ThisBuild / run / connectInput := true
ThisBuild / run / fork := true

Compile / run / connectInput := true
Compile / run / fork := true

Test / run / connectInput := true
Test / run / fork := true

Compile / console / fork := true
Compile / run / envVars ++= Map(
  // adjust path to wherever you put the two native libs
  "LD_LIBRARY_PATH" -> (baseDirectory.value / "lib" / platform).getAbsolutePath,
  "DYLD_LIBRARY_PATH" -> (baseDirectory.value / "lib" /  platform).getAbsolutePath,
  "PATH" -> {
    val p = (baseDirectory.value / "lib").getAbsolutePath
    sys.env.get("PATH").fold(p)(old => s"$p${java.io.File.pathSeparator}$old")
  }
)
Compile / run / javaOptions ++= Seq(
  s"-Djava.library.path=${(baseDirectory.value / "lib" / platform).getAbsolutePath}"
)

run / envVars ++= Map(
  "LD_LIBRARY_PATH" -> (baseDirectory.value / "lib" / platform).getAbsolutePath,
  "DYLD_LIBRARY_PATH" -> (baseDirectory.value / "lib" /  platform).getAbsolutePath,
  "PATH" -> {
    val p = (baseDirectory.value / "lib").getAbsolutePath
    sys.env.get("PATH").fold(p)(old => s"$p${java.io.File.pathSeparator}$old")
  }
)
run / javaOptions ++= Seq(
  s"-Djava.library.path=${(baseDirectory.value / "lib" / platform).getAbsolutePath}"
)


sourceGenerators in Test += Def.task {
  val file = (sourceManaged in Test).value / "amm.scala"
  IO.write(file, """object amm extends App { ammonite.AmmoniteMain.main(args) }""")
  Seq(file)
}.taskValue

// Optional, required for the `source` command to work
(fullClasspath in Test) ++= {
  (updateClassifiers in Test).value
    .configurations
    .find(_.configuration.name == Test.name)
    .get
    .modules
    .flatMap(_.artifacts)
    .collect { case (a, f) if a.classifier == Some("sources") => f }
}

lazy val root = (project in file("."))
  .settings(
    name := "Tempura"
  )
