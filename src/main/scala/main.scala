
import clojure.lang.{RT, Symbol}

object main {

  ////////////////
  // Clojure-specific environmental variables
  //
  private val REQUIRE = RT.`var`("clojure.core", "require")
  private val CLOJURE_MAIN = Symbol.intern("clojure.main") // entry to clojure repl
  private val MAIN = RT.`var`("clojure.main", "main")
  private val CMD =
    "(require '[clojure.main :as m])\n" +
      "(m/repl :init #(apply require m/repl-requires)\n" +
      ":eval (fn [expr] (tempura.cozy.CS/eval expr))\n  " +
      "))"

  @main def start() : Unit = {
    val a = " "
    val args = a.split(" ") ++ List("-e", CMD)// "(tempura.cozy.CS/convert '(+ 1 2 3))")
    println(" ------------------------------------------- ")
    println(" -----------  Starting Cozy REPL  ---------- ")
    println(" ------------------------------------------- ")
    RT.init()
    REQUIRE.invoke(CLOJURE_MAIN)
    MAIN.applyTo(RT.seq(args))
    println(" ------------------------------------------- ")
    println(" -----------  Quitting Cozy REPL  ---------- ")
    println(" ------------------------------------------- ")
  }

}