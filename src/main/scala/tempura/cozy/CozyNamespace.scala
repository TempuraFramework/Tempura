package tempura.cozy
import clojure.lang.{Symbol, *}
import tempura.expression.Core
import tempura.smt.SmtSolver.SolverEnvironment


import scala.collection.mutable.{ListBuffer, HashMap as HM}
import scala.collection.mutable
import clojure.lang.RT.{CURRENT_NS, `var` as rt_var}


// wrapper around a user-created namespace object
// the variables (_typeEnv, _interpEnv, _solvers) constitute the shadow-state
// CAUTION: caller to the constructor is required to clone typeEnv, interpEnv, solvers
case class CozyNamespace(ns: Namespace, typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv, solvers: mutable.HashMap[String, SolverEnvironment]) {
  self =>
  private final val typeEnvC = rt_var(ns.getName.getName, "_typeEnv", typeEnv)
  private final val interpEnvC = rt_var(ns.getName.getName, "_interpEnv", interpEnv)
  private final val solversC = rt_var(ns.getName.getName, "_solvers", solvers)

  def this(ns: Namespace, typeEnv: Core.TypeEnv, interpEnv: Core.InterpEnv) = {
    this(ns, typeEnv, interpEnv, mutable.HashMap.empty[String, SolverEnvironment])
  }

  def getNamespace: Namespace = ns

  def getTypeEnv: Core.TypeEnv = typeEnvC.get().asInstanceOf[Core.TypeEnv]

  def getInterpEnv: Core.InterpEnv = interpEnvC.get().asInstanceOf[Core.InterpEnv]

  def getSolverEnvs: HM[String, SolverEnvironment] = solversC.get().asInstanceOf[HM[String, SolverEnvironment]]

  def findSolverEnv(name: String): Option[SolverEnvironment] = getSolverEnvs.get(name)

  def addSolverEnv(name: String, env: SolverEnvironment): Unit = getSolverEnvs.update(name, env)

}
