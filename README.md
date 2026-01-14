# Tempura Framework for First-order Transition Systems Verification

Tempura is a framework for verifying transition systems written in multi-sorted first-order logic with arrays, uninterpreted functions, and equality. Tempura is written fully in Scala 3 and is designed to be highly modular, with each component of Tempura being reusable as a library providing value independently, while providing even more value when used as a whole. 

In particular, Tempura includes:
 - A dependently typed, extensible intermediate representation for first-order formulas and terms with HOAS-style evaluation; dependent typing is simulated using a combination of GADTs, F-bounded polymorphism, and existential containers (https://dl.acm.org/doi/pdf/10.1145/3679007.3685056). Terms in Tempura's IR are type-safe up to the first-order, with arguments for lambda/function terms being checked at runtime (mostly due to the fact that we cannot statically infer the number of arguments for a function definition at compile-time, and Scala 3 tuples are somewhat inflexible for this purpose).
 - A type-safe, extensible SMT solver library supporting interaction with Z3, SmtInterpol, CVC5, and generic SMTLIB-based solvers via stdin/out. The existing backends support reasoning with the full theory of arrays (+ function spaces in Z3), datatypes, finite-universe sorts, uninterpreted functions, and a wee bit of arithmetic.
 - An interpolation interface for SMT solver-independent interpolation support. Currently this implemented by either spinning up a fresh solver that supports interpolation (either SMTInterpol or CVC5), by doing quantifier elimination, which is solver-independent but requires the underlying solver to support QE, and Zipper interpolation for propositional formulas (https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-zipint.pdf).
 - Configurable algorithms for explicit-state model checking with both forward-mode and backward-mode search.
 - A command-line read-eval-print-loop interface that supports taking in a transition system described in a VMT-like description language and perform verification tasks on it;

### Input format

Tempura takes in either a transition-system description in VMT format or the following file format which we call transition description language (TDL).
A `.tdl` file consists of the following S-expression blocks:
```
(vmtlib (<vmtlib expression>)
(sort <sortname>) 
(finite-sort <sortname> <size>)
(var <name> <sort>)
(var <name <sort> <def>)
(fun <name> <sort>)
(fun <name <sort> <def>)
(state-var <name> <sort> :next <next state name>)
(transition-var <name> <sort>)
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

### Formula and Sort Definition Syntax

Formulas are assumed to be written in SMTLIB syntax. Sort definitions are also mostly SMTLIB compliant except function sorts can be defined via the syntax `(-> dom1 dom2 ... domn range)`, but function symbols _must_ be defined using the `fun` keyword instead of the `var` keyword. Every variable or function definition induces a background axiom in the underlying solver, and hence, this is no different than first declaring a theory symbol and then writing a theory axiom for it suing the `(var <name> <sort>)` and `(theory-axiom ...)` syntax.

### System Model

In TDL a transition system is a tuple $(\mathbb{S}, X_S, X_{Tr}, X_{Th}, Th, Init, Tr)$ where $\mathbb{S}$ is a set of sorts, either of a finite universe size (specified using `finite` block) or uninterpreted (specified using the `sort`) block. Altogether $X_S \cup X_{Tr} \cup X_{Th}$ is the vocabulary. $X_S$ is a set of _state variables_ which have primed copies in the transition. $X_{Tr}$ is a set of _transition variables_ that don't have primed copies, and only appear as existentially quantified symbols in the transition formula. $X_{Th}$ is a set of _theory symbols_ that appear in the theory axioms but is otherwise immutable during the execution of the transition system. $Th$ is a set of first-order formulas over $X_{Th}$ that axiomatizes the background theory --- for instance, we can introduce a linear order symbol $\succ : \mathbb{S} \times \mathbb{S} \to \mathbb{B}$ for a particular sort $\mathbb{S} \in \mathbb{S}$ by appropriately axiomatizing the symbol $\succ \in X_{Th}$. $Init(X_S)$ is an initial condition describing how the transition system is initialized, and $Tr(X_S, X_{Tr}, X_S')$ is the transition formula that describes transition from a state described by $X_S$ into a state described by $X_S'$, with variables in $X_{Tr}$ being implicitly existentially quantified. A _run_ in the transition system is a sequence of states $s_0,...,s_n$, where each state is over $X_S$ and $s_0 \vDash Init$ and $\forall 0\leq i < n. s_i \wedge \exists X_{Tr}. Tr \vDash s_{i+1}')$.

Variables in $X_S$ and $X_{Tr}$ are specified by the user using either the `(state-var ...)` or the `(transition-var ...)` blocks, correspondingly. Variables in $X_Th$ are implicitly determined by our tool; essentially any free variable in the `(theory-axiom ...)` definitions are taken as an element of $X_{Th}$. We require that $X_S$, $X_{Tr}$, and $X_{Th}$ are disjoint sets.

### Safety properties in TDL
Each safety property is specified using a `(property ...)` block. Blocks under the same name are taken conjunctively as a single property, and blocks of different names are taken as different safety proof goals (similar to Ivy) that can then be verified using assume-guarantee reasoning. The model checker must then guarantee that, for proof goals $\phi_1,...,\phi_n$, $\forall i. \forall j. \{\phi_j;j\neq i\}\vDash \square \phi$ holds for the given transition system.

### Liveness properties in TDL

The S-expression blocks in TDL `live-property`, `live-assumption`, `fair-assumption` correspond to stating, as a proof goal, a liveness property of form $GF (r) \to G(p \to F q))$ where $G$ and $F$ are LTL globally and eventually operators. The $r$ term here corresponds to a fairness assumption that is toggled infinitely often, `p` is a liveness assumption that describes the pending states of the system, and $q$ is the eventuality that we must reach. Each (fair-assumption, live-assumption, live-property) triple under the same name are grouped together to form the final liveness proof goal, and in case there are multiple unnamed blocks of the same name, they are taken conjunctively to form a single property.

It is possible that a liveness property is specified without a corresponding liveness assumption, or a corresponding fairness assumption, or both. This corresponds to different forms of the general liveness formula described above: If the property doesn't have a liveness assumption then we're verifying $GF(r) \to GF(q)$; if the property doesn't have a fairness assumption then we're verifying $G(p \to F(q))$, or if the property lacks any assumptions we are just checking termination: $GF(q)$. 

On the model checker side, and different from safety properties, we are not going to support assume-guarantee reasoning involving multiple liveness properties yet. This might change in the future. 

### The Cozy User Interface

The REPL feature of Tempura implements a DSL called Cozy, which is embedded inside Clojure. The following is an incomplete list of functions one can call inside the REPL in Clojure fashion. The functions allow the REPL user to manipulate Tempura's library routines in a Clojure-esque way, and are organized into three namespaces:
 - the `c` namespace, which contains some generic formula and sort manipulation routines
 - the `c.solver` namespace, which bridges Tempura's SMT solver interface with Cozy
 - the `c.solverOps` namespace, which consists of a set of routines to compile a Tempura IR formula to a SMT solver's own representation (called "lowering") and back (called "lifting")
 - the `c.transforms` namespace, which plugs into all transformations one can do on objects inside Tempura

#### The `c` Namespace 
***Creating sorts***
 ```
  (c/sort 'SortName)                    ; Create uninterpreted sort
  (c/finite-sort 'SortName size)        ; Create finite universe sort (size: integer)
```
***Creating variables and definitions***
```
  (c/var 'varName 'SortExpr)            ; Declare uninterpreted variable
  (c/var 'varName '(Array Int Bool))    ; Example: array variable
  (c/def 'varName expr)                 ; Define interpreted variable with expression
```
***Creating expressions***
```
  (c/expr '(and x y))                   ; Parse S-expression to Core.BoxedExpr
  (c/expr '(forall ((x Int)) (> x 0)))  ; Quantified formula
```

#### The `c.solver` Namespace
***Creating solvers***
```
  (c.solver/create 'z3 :nickname)       ; Create Z3 solver (keyword for name)
  (c.solver/create 'cvc5 :s1)           ; Create CVC5 solver
  (c.solver/create 'smtinterpol :si)    ; Create SMTInterpol solver
```
***Environments***
 
 All variables that have a corresponding representation inside the solver are stored in an `interp-env`. All sort definitions are stored in a `type-env`. There is a unique `interp-env` and `type-env` associated with each Clojure namespace.
 ```
  (c.solver/interp-env)                 ; Get context of all variables from current namespace
  (c.solver/type-env)                   ; Get context of all sorts from current namespace
 ```
***Solver operations***

 The following is a list of solver operations generic to any SMT solver Tempura supports.
 ```
  (c.solver/push solver)                ; Push solver context
  (c.solver/pop solver)                 ; Pop solver context
  (c.solver/reset solver)               ; Reset solver state
  (c.solver/add-constraint solver expr) ; Add single constraint (BoxedExpr)
  (c.solver/add-constraints solver '(expr1 expr2 ...)) ; Add list of constraints

  (c.solver/check-sat solver)           ; Returns :sat, :unsat, or :unknown
  (c-solver-solve-once solver expr)     ; Check sat with push/pop (user namespace)


  (c.solver/model solver)               ; Get model if SAT (returns Model or nil)
  (c.solver/unsat-core solver)          ; Get unsat core if UNSAT (returns UnsatCore or nil)


  (c.solver/fork solver)                ; Create independent copy of solver
  (c.solver/history solver)             ; Get command history as list
  (c.solver/init solver :lia)           ; Initialize logic (:lia, :nia, or :arith-free)
```

#### The `c.solverOps` Namespace

This namespace contains a set of routines for solver oprations including lowering (compiling from an expression in Tempura IR to an expression in the backend SMT solver's format) and lifting (compiling from an expression in backend SMT solver's format back to Tempura IR).

```
  (c.solverOps/lower solver expr)       ; Lower Core expr to solver term
  (c.solverOps/lift solver term)        ; Lift solver term to Core expr
  (c.solverOps/lift-sort solver sort)   ; Lift solver sort to Core sort
  (c.solverOps/lift-def solver func)    ; Lift solver func decl to Core expr

  (c.solverOps/declare-var solver "varName" sort)    ; Declare uninterpreted var
  (c.solverOps/define-var solver "varName" expr)     ; Define var, returns [decl axioms]
  (c.solverOps/define-sort solver sort)              ; Define sort in solver
  (c.solverOps/lower-sort solver sort)               ; Lower sort to solver sort
```
  
#### Namespace: c.transforms (Dynamic Transforms)

  All registered transforms from Registry are available as variadic functions:
  (c.transforms/transform-name arg1 arg2 ...)  ; Call registered transform


### Some Cozy Usage Examples

***Formula and sort manipulation***
```
  (c/sort 'Node)
  (c/finite-sort 'Color 3)
  (c/var 'x 'Int)
  (c/var 'nodes '(Array Int Node))
```

***Creating and using a solver***
```
  (def s (c.solver/create 'z3 :my-solver))
  (c.solver/init s :lia)

  ;; Add constraints
  (def constraint (c/expr '(> x 0)))
  (c.solver/add-constraint s constraint)
  (c.solver/push s)
  (c.solver/add-constraint s (c/expr '(< x 10)))

  ;; Check satisfiability
  (c.solver/check-sat s)  ; => :sat

  ;; Get model
  (def m (c.solver/model s))

  ;; Clean up
  (c.solver/pop s)
```

### Cozy Syntax
Cozy syntax is just Clojure syntax:

  | Argument Type      | Syntax   | Example                 |
  |--------------------|----------|-------------------------|
  | Sort/Variable name | 'name    | 'Int, 'myVar            |
  | Solver backend     | 'name    | 'z3, 'cvc5              |
  | Solver nickname    | :keyword | :s1, :my-solver         |
  | Logic type         | :keyword | :lia, :nia, :arith-free |
  | Result value       | :keyword | :sat, :unsat, :unknown  |
  | String literal     | "string" | "varName"               |



### More details
Forthcoming


