package tempura.cozy

import clojure.lang.{AFn, ISeq, Namespace, Symbol, Var, RT}
import scala.quoted.*

object CozyFunction {

  /**
   * Macro-based utilities for creating and registering Clojure functions from Scala.
   *
   * Usage examples:
   * {{{
   *   // Nullary function: (my-func)
   *   cozyFunction("my-func", "user") { () =>
   *     "Hello from Clojure!"
   *   }
   *
   *   // Unary function: (add-one x)
   *   cozyFunction("add-one", "user") { (x: AnyRef) =>
   *     x.asInstanceOf[Long] + 1
   *   }
   *
   *   // Binary function: (add x y)
   *   cozyFunction("add", "user") { (x: AnyRef, y: AnyRef) =>
   *     x.asInstanceOf[Long] + y.asInstanceOf[Long]
   *   }
   *
   *   // Ternary function: (add3 x y z)
   *   cozyFunction("add3", "user") { (x: AnyRef, y: AnyRef, z: AnyRef) =>
   *     x.asInstanceOf[Long] + y.asInstanceOf[Long] + z.asInstanceOf[Long]
   *   }
   *
   *   // Variadic function: (my-sum & args)
   *   cozyFunctionVariadic("my-sum", "user") { (args: Seq[AnyRef]) =>
   *     args.map(_.asInstanceOf[Long]).sum
   *   }
   * }}}
   */

  /**
   * Create and register a nullary Clojure function.
   * Callable from Clojure as: (func-name)
   */
  inline def cozyFunction(
                              inline name: String,
                              inline namespace: String = "user"
                            )(inline body: () => AnyRef): Var =
    ${ clojureFunctionImpl0('name, 'namespace, 'body) }

  /**
   * Create and register a unary Clojure function.
   * Callable from Clojure as: (func-name arg)
   */
  inline def cozyFunction1(inline name: String, inline namespace: String = "user")(inline body: AnyRef => AnyRef): Var =
    ${ clojureFunctionImpl1('name, 'namespace, 'body) }

  /**
   * Create and register a binary Clojure function.
   * Callable from Clojure as: (func-name arg1 arg2)
   */
  inline def cozyFunction2(inline name: String, inline namespace: String = "user")(inline body: (AnyRef, AnyRef) => AnyRef): Var =
    ${ clojureFunctionImpl2('name, 'namespace, 'body) }

  /**
   * Create and register a ternary Clojure function.
   * Callable from Clojure as: (func-name arg1 arg2 arg3)
   */
  inline def cozyFunction3(
                               inline name: String,
                               inline namespace: String = "user"
                             )(inline body: (AnyRef, AnyRef, AnyRef) => AnyRef): Var =
    ${ clojureFunctionImpl3('name, 'namespace, 'body) }

  /**
   * Create and register a variadic Clojure function.
   * Callable from Clojure as: (func-name arg1 arg2 ... argN)
   */
  inline def cozyFunctionVariadic(
                                      inline name: String,
                                      inline namespace: String = "user"
                                    )(inline body: Seq[AnyRef] => AnyRef): Var =
    ${ clojureFunctionVariadicImpl('name, 'namespace, 'body) }

  // Macro implementations

  private def clojureFunctionImpl0(
                                    name: Expr[String],
                                    namespace: Expr[String],
                                    body: Expr[() => AnyRef]
                                  )(using Quotes): Expr[Var] = {
    '{
      val fn = new AFn {
        override def invoke(): Object = $body()
      }
      register($namespace, $name, fn)
    }
  }

  private def clojureFunctionImpl1(
                                    name: Expr[String],
                                    namespace: Expr[String],
                                    body: Expr[AnyRef => AnyRef]
                                  )(using Quotes): Expr[Var] = {
    '{
      val fn = new AFn {
        override def invoke(arg1: Object): Object = $body(arg1)
      }
      register($namespace, $name, fn)
    }
  }

  private def clojureFunctionImpl2(
                                    name: Expr[String],
                                    namespace: Expr[String],
                                    body: Expr[(AnyRef, AnyRef) => AnyRef]
                                  )(using Quotes): Expr[Var] = {
    '{
      val fn = new AFn {
        override def invoke(arg1: Object, arg2: Object): Object =
          $body(arg1, arg2)
      }
      register($namespace, $name, fn)
    }
  }

  private def clojureFunctionImpl3(
                                    name: Expr[String],
                                    namespace: Expr[String],
                                    body: Expr[(AnyRef, AnyRef, AnyRef) => AnyRef]
                                  )(using Quotes): Expr[Var] = {
    '{
      val fn = new AFn {
        override def invoke(arg1: Object, arg2: Object, arg3: Object): Object =
          $body(arg1, arg2, arg3)
      }
      register($namespace, $name, fn)
    }
  }

  private def clojureFunctionVariadicImpl(
                                           name: Expr[String],
                                           namespace: Expr[String],
                                           body: Expr[Seq[AnyRef] => AnyRef]
                                         )(using Quotes): Expr[Var] = {
    '{
      val fn = new AFn {
        override def applyTo(arglist: ISeq): Object = {
          val args = scala.collection.mutable.ArrayBuffer[AnyRef]()
          var current = arglist
          while (current != null) {
            args += current.first().asInstanceOf[AnyRef]
            current = current.next()
          }
          $body(args.toSeq)
        }
      }
      register($namespace, $name, fn)
    }
  }

  /**
   * Helper function to register a function in a Clojure namespace.
   * Returns the created Var.
   */
  private def register(namespace: String, name: String, fn: AFn): Var = {
    val ns = Namespace.findOrCreate(Symbol.intern(namespace))
    Var.intern(ns, Symbol.intern(name), fn)
  }

}
