# Repository Guidelines

## Project Structure & Module Organization
Core Scala 3 sources live in `src/main/scala`, with `main.scala` exposing the TempuScript REPL entrypoint. Place new modules under descriptive packages rather than expanding `main.scala`. Tests belong in `src/test/scala`; mirror the package path of the code under test. Native solver binaries live under `lib/<platform>` (Linux and macOS builds are checked in). Sample VMT inputs are in `examples/`, and sbt build metadata sits in `project/`.

## Build, Test, and Development Commands
Use `sbt compile` to resolve dependencies and catch type errors. Run `sbt run` to launch TempuScript; it automatically wires the solver libraries listed in `build.sbt`. Execute `sbt test` before every push; add `~test` for a watch mode while iterating. `sbt pPrint` echoes the active platform and library paths—handy when verifying solver setup.

## Coding Style & Naming Conventions
Follow idiomatic Scala 3 style: two-space indents, primary constructors on the same line as class names, and given/using syntax where applicable. Prefer pure functions and keep side effects localized to REPL orchestration. Name files after the primary class or object (`FooSolver.scala`), and favor camelCase for values/methods, PascalCase for types. There is no scalafmt config yet; match existing formatting when in doubt.

## Testing Guidelines
Write ScalaTest suites (`SomethingSuite`) under `src/test/scala`, grouping related behavior into `describe`/`it` or `FunSuite` style blocks. Leverage ScalaCheck generators when validating parser and solver contracts; property tests should accompany complex logic. Keep tests deterministic and document unusual fixtures. Run `sbt test` locally and ensure new scenarios cover edge cases introduced by the change.

## Commit & Pull Request Guidelines
Follow the short imperative style already in history (`add claude-generated stubs`, `change solver API`). Scope commits narrowly and include context in the body if behavior changes or migrations are required. For PRs, provide a succinct summary, link to any tracking issues, list validation commands (`sbt compile`, `sbt test`), and add screenshots or transcripts when altering REPL behavior. Highlight solver/library updates so reviewers can double-check platform compatibility.

## Solver & Environment Setup
The sbt build exports `LD_LIBRARY_PATH`, `DYLD_LIBRARY_PATH`, and `java.library.path` for you, but ensure the matching solver binaries exist under `lib/<platform>`. When working on new platforms, duplicate one of the existing directories and drop in the correct Z3 artifacts. Avoid committing large binaries; coordinate with maintainers if new solvers or versions are needed.
