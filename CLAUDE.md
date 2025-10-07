# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Tempura is a Scala 3 (3.7.3) model checker and verification tool built on SMT solving. It provides:
- A strongly-typed intermediate representation (IR) for SMT formulas with dependent types
- Support for transition systems via VMT (Verification Modulo Theories) format
- Multiple SMT solver backends (Z3, CVC5, SMTInterpol)
- An interactive REPL (TempuScript) for verification tasks
- Abstract interpretation utilities via Galois connections and abstract domains

## Build Commands

**Compile:**
```bash
sbt compile
```

**Run tests:**
```bash
sbt test
```

**Run a specific test:**
```bash
sbt "testOnly org.abstractpredicates.parsing.ParserTests"
```

**Start TempuScript REPL:**
```bash
sbt run
```

**Start Ammonite console (for debugging):**
```bash
sbt "test:run"
```

## Architecture

### Core Expression IR (`org.abstractpredicates.expression.Core`)

The heart of the system is a strongly-typed expression AST with dependent types:
- **Sorts**: `BoolSort`, `NumericSort`, `ArraySort[D, R]`, `FunSort[R]`, `UnInterpretedSort`, `DatatypeConstructorSort`, `FiniteUniverseSort`, `AliasSort[S]`
- **Expressions**: `Expr[A <: Sort[A]]` - all expressions are parametrized by their sort
- **Boxing**: `BoxedSort` and `BoxedExpr` for existential quantification over sorts
- **Env**: Mutable environment class used for both `TypeEnv` (name → BoxedSort) and `InterpEnv` (name → BoxedExpr)

Key design choices:
- Functions are first-order: represented as `Macro[Y]` (function with definition) or `Var[FunSort[Y]]` (uninterpreted function)
- The IR supports higher-order syntax but solver-related facilities only handle first-order fragments
- `Substitute[Y]` nodes represent function application by inlining macro bodies with variable bindings

### SMT Solver Interface (`org.abstractpredicates.smt.SmtSolver`)

Solver-agnostic interface with three key traits:
- **Solver[T]**: Core interface with lowering/lifting between IR and solver-specific terms
  - `lowerSort`, `defineSort`: Convert Core sorts to solver sorts
  - `lower`: Convert Core expressions to solver terms
  - `liftTerm`, `liftSort`, `liftFunc`: Convert solver objects back to IR
  - `declareVar`, `defineVar`: Introduce new symbols (uninterpreted vs. defined)
  - `add`, `push`, `pop`, `checkSat`: Standard SMT operations
- **Model[SOLVER]**: Represents satisfying assignments
- **Translator**: Bidirectional conversion between IR and solver representations

Z3 implementation (`org.abstractpredicates.smt.Z3Solver`):
- Uses hash-consing via mutable maps: `exprMap`, `sortMap`, `funcMap`
- Update hooks on `TypeEnv`/`InterpEnv` automatically translate additions into Z3 declarations
- Native library loading configured via `lib/linux-x86_64/` or `lib/macos-arm64/` (set in build.sbt)

### Parsing Pipeline (`org.abstractpredicates.parsing`)

**Three-stage parsing:**
1. `StringToSExprParser`: String → `ParseTree` (S-expression AST)
2. `VMTParser`: `ParseTree` → typed `Core.Expr[T]` (parses VMT commands into IR)
3. `TransitionSystemReader`: Assembles parsed declarations into `TransitionSystem` objects

**Key files:**
- `parsers/StringToSExprParser.scala`: Cats-parse based S-expression parser
- `ast/VMTParser.scala`: Type-directed parser from S-expressions to Core IR
- `io/TransitionSystemReader.scala`: Orchestrates parsing of .vmt files into transition systems

### Transition Systems (`org.abstractpredicates.transitions`)

**TransitionSystem** class encapsulates:
- `stateVars: List[TimedVariable]` - state variables and their next-state counterparts
- `init: Expr[BoolSort]` - initial condition
- `trans: Expr[BoolSort]` - transition relation (over current + next state)
- `assertions`, `assumptions`, `liveAssertions`, `liveAssumptions`, `fairness`
- `typeEnv`, `interpEnv` - type and interpretation environments

**TimedVariable** represents state variables with optional next-state versions for transition encoding.

### REPL (`org.abstractpredicates.repl`)

Built on Ammonite terminal framework:
- **TempuScriptMain**: Main REPL loop with custom filters (tab completion, history, multiline)
- **TempuCommandDispatcher**: Routes S-expression commands to handlers
- **CommonCommands**: Built-in commands like `:history`, `:parse`, `:vmt`, `:exit`, `:read-ts`
- **TempuScriptState**: Maintains REPL history and state

Input is parsed as S-expressions, then dispatched to command handlers.

### Abstract Interpretation (`org.abstractpredicates.abstraction`)

- **AbstractDomain**: Lattice-based abstract domains with join/meet/widening
- **GaloisConnection**: Abstraction/concretization pairs with soundness proofs
- **IntervalDomain**: Numeric interval abstraction
- **IdempotentSemiring**, **StarSemiring**: Algebraic structures for program analysis

## Important Conventions

### Environment Management
- Environments (`TypeEnv`, `InterpEnv`) are mutable and support update hooks
- Solvers register hooks to auto-translate environment updates into solver declarations
- Use `env.newType(sort)`, `env.newVar(expr)` to register new symbols
- Use `env ++@ otherEnv` to merge environments (right side takes precedence)

### Sort Unification
- Use `sort.unify(otherSort)` to attempt unification between sorts
- `BoxedSort`/`BoxedExpr` are used when sort information must be existentially quantified
- Use `.box()` extension method to box expressions/sorts, `.unbox` to unbox

### Function Handling
- First-order only: functions cannot be passed as arguments
- Use `Macro[Y]` for defined functions (with body)
- Use `Var[FunSort[Y]]` for uninterpreted function symbols
- `Substitute[Y]` represents function application (macro expansion)

### Native Library Setup
- Z3 and CVC5 native libraries in `lib/platform/` directories
- Platform detection in build.sbt sets `LD_LIBRARY_PATH`/`DYLD_LIBRARY_PATH`
- Must run with `fork := true` and `connectInput := true` for proper loading

## Testing
Tests use ScalaTest + ScalaCheck:
- `parsing/ParserTests.scala` - S-expression parsing
- `parsing/VMTParserTests.scala` - VMT format parsing
- `smt/Z3BackendTests.scala` - Z3 solver integration
- `expression/CoreExprsTest.scala` - IR expression tests
- `expression/EqualityTests.scala` - Sort/expression equality

## Examples
Example VMT files in `examples/` directory (currently: `ranking_infer1.vmt`)
