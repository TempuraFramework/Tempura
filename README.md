# Tempura Framework for First-order Transition Systems Verification

Tempura is a framework for verifying transition systems written in multi-sorted first-order logic with arrays, uninterpreted functions, and equality. Tempura is written fully in Scala 3 and is designed to be highly modular, with each component of Tempura being reusable as a library providing value independently, while providing even more value when used as a whole. 

In particular, Tempura includes:
 - A dependently typed, extensible intermediate representation for first-order formulas and terms with HOAS-style evaluation; dependent typing is simulated using a combination of GADTs, F-bounded polymorphism, and existential containers (https://dl.acm.org/doi/pdf/10.1145/3679007.3685056). Terms in Tempura's IR are type-safe up to the first-order, with arguments for lambda/function terms being checked at runtime (mostly due to the fact that we cannot statically infer the number of arguments for a function definition at compile-time, and Scala 3 tuples are somewhat inflexible for this purpose).
 - A type-safe, extensible SMT solver library supporting interaction with Z3, SmtInterpol, CVC5, and generic SMTLIB-based solvers via stdin/out. The existing backends support reasoning with the full theory of arrays (+ function spaces in Z3), datatypes, finite-universe sorts, uninterpreted functions, and a wee bit of arithmetic.
 - An interpolation interface for SMT solver-independent interpolation support. Currently this implemented by either spinning up a fresh solver that supports interpolation (either SMTInterpol or CVC5) or by doing quantifier elimination, which is solver-independent but requires the underlying solver to support QE.
 - Configurable algorithms for explicit-state model checking with both forward-mode and backward-mode search.
 - A command-line read-eval-print-loop interface that supports taking in a transition system described in a VMT-like description language and perform verification tasks on it;

### Input format

Tempura takes in either a transition-system description in VMT format or the following file format which we call transition description language (TDL).
A `.tdl` file consists of the following S-expression blocks:
```
(vmtlib (<vmtlib expression>)
(declare-sort <sortname>) | (declare-sort <sortname> :projectable)
(declare-finite-sort <sortname> <size>)
(state-var <name> <sort> :next <next state name>)
(init <initial condition>)
(transition <transition>)
(transition <transition> :name <name>) ;; multiple transitions are allowed, they are taken to be a big disjunction
(theory-axiom <formula>)
(theory-axiom <formula> :name <name>) ;; multiple axioms are allowed
(property <property formula>)
(property <proper formula> :name <name>) ;; multiple properties are allowed
(assumption <assumption formula>)
(assumption <assumption formula> :name <name>) ;; multiple assumptions are allowed
(live-property <liveness property formula>)
(live-property <liveness property formula> :name <name>)
(live-assumption <liveness assumption formula>)
(live-assumption <liveness assumption formula> :name <name>)
(fair-assumption <fairness assumption formula>)
(fair-assumption <fairness assumption formula> :name <name>)
```
An example of VMT <-> TDL correspondence may be found in the `examples/` folder.

### More details
Forthcoming


