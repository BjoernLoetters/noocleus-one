package noocleus.semantic

import cats.effect.IO
import cats.effect.concurrent.Ref
import noocleus.syntax.Tree
import cats.implicits._

object TypeAnalysis {
  
  private sealed trait Expectation[T] extends Product with Serializable {
    
    def get: TypeCheck[T]
    
  }
  
  private object Expectation {
    
    case class Check[T](value: T) extends Expectation[T] {
      lazy val get: TypeCheck[T] =
        TypeCheck.pure(value)
    }
    
    case class Infer[T](reference: Ref[IO, T]) extends Expectation[T] {
      
      lazy val get: TypeCheck[T] =
        TypeCheck.lift(reference.get)
      
    }
    
    def empty[T >: Null]: TypeCheck[Expectation[T]] =
      TypeCheck.lift(Ref.of[IO, T](null)).map(Infer(_))
    
  }
  
  /**
   * Infers the sigma type of the `tree`
   * @param tree The `tree`
   * @return The sigma type of the provided `tree`
   */
  def inferSigma(tree: Tree): TypeCheck[Type.Sigma] =
    for {
      inference <- Expectation.empty[Type.Sigma]
      _ <- analyseSigma(tree, inference)
      result <- inference.get
    } yield result
  
  /**
   * Infers the the tau type of the `tree`
   * @param tree The `tree`
   * @return The tau type of the provided `tree`
   */
  private def inferTau(tree: Tree): TypeCheck[Type.Tau] =
    for {
      inference <- Expectation.empty[Type.Tau]
      _ <- analyseTau(tree, inference)
      result <- inference.get
    } yield result
  
  /**
   * Fulfills the expectation, i.e. either infers the `tau` type (generalized
   * to a sigma type) or checks if an instance of the provided sigma type
   * (obtained from the expectation value) can be unified with the `tau` type.
   * @param tau The `tau` type
   * @param expectation The expectation
   * @return This function returns nothing since the result is inferred as a
   *         side effect
   */
  private def fulfillSigma(tau: Type.Tau, expectation: Expectation[Type.Sigma]): TypeCheck[Unit] =
    expectation match {
      case Expectation.Check(sigma) =>
        for {
          tau0 <- TypeCheck.instantiate(sigma)
          _ <- fulfillTau(tau, Expectation.Check(tau0))
        } yield ()
      case Expectation.Infer(reference) =>
        for {
          sigma <- TypeCheck.generalize(tau)
          _ <- TypeCheck.lift(reference.set(sigma))
        } yield ()
    }
  
  /**
   * Fulfills the expectation, i.e. either infers the `tau` type or checks if
   * the provided tau type (obtained from the expectation value) can be unified
   * with the `tau` type.
   * @param tau The `tau` type
   * @param expectation The expectation
   * @return This function returns nothing since the result is inferred as a
   *         side effect
   */
  private def fulfillTau(tau: Type.Tau, expectation: Expectation[Type.Tau]): TypeCheck[Unit] =
    expectation match {
      case Expectation.Check(tau0) =>
        TypeCheck.unify(tau, tau0)
      case Expectation.Infer(reference) =>
        TypeCheck.lift(reference.set(tau))
    }
  
  /**
   * Analyses (i.e. either infers or checks, depending on the provided `expectation`)
   * the given `tree`
   * @param tree The `tree`
   * @param expectation The expectation
   * @return This function returns nothing since the result is inferred as a
   *         side effect
   */
  private def analyseSigma(tree: Tree, expectation: Expectation[Type.Sigma]): TypeCheck[Unit] =
    for {
      inference <- Expectation.empty[Type.Tau]
      _ <- analyseTau(tree, inference)
      tau <- inference.get
      _ <- fulfillSigma(tau, expectation)
    } yield ()
  
  /**
   * Analyses (i.e. either infers or checks, depending on the provided `expectation`)
   * the given `tree`
   * @param tree The `tree`
   * @param expectation The expectation
   * @return This function returns nothing since the result is inferred as a
   *         side effect
   */
  private def analyseTau(tree: Tree, expectation: Expectation[Type.Tau]): TypeCheck[Unit] =
    tree match {
      case Tree.Variable(name) =>
        for {
          sigma <- TypeCheck.lookup(name)
          tau <- TypeCheck.instantiate(sigma)
          _ <- fulfillTau(tau, expectation)
        } yield ()
  
      case Tree.Application(function, argument) =>
        for {
          tau0 <- inferTau(function)
          tau1 <- inferTau(argument)
          tau <- TypeCheck.newMetaVariable
          _ <- TypeCheck.unify(tau0, tau1 --> tau)
          _ <- fulfillTau(tau, expectation)
        } yield ()
  
      case Tree.Abstraction(binder, body) =>
        for {
          inference <- Expectation.empty[Type.Tau]
          codomain <- bindTau(binder, inference)(inferTau(body))
          domain <- inference.get
          _ <- fulfillTau(domain --> codomain, expectation)
        } yield ()

      case Tree.Data(typeName, typeParameters, constructors, body) =>
        
        def go[A](constructors: List[Tree.Constructor])(continue: TypeCheck[A]): TypeCheck[A] =
          constructors match {
            case Nil => continue
            case Tree.Constructor(name, types) :: constructors =>
              val resultType = typeParameters.foldLeft[Type.Sigma](typeName)(Type.Application)
              val constructorType = types.foldRight(resultType)(_ --> _)
              TypeCheck.enter(name, Type.ForAll(typeParameters, constructorType))(go(constructors)(continue))
          }
  
        go(constructors)(analyseTau(body, expectation))

      case Tree.Match(tree, cases) =>
        
        for {
          tau0 <- inferTau(tree)
          tau1 <- expectation match {
            case Expectation.Check(tau) =>
              TypeCheck.pure(tau)
            case Expectation.Infer(ref) =>
              for {
                tau <- TypeCheck.newMetaVariable
                _ <- TypeCheck.lift(ref.set(tau))
              } yield tau
          }
          _ <- {
            def go[A](cases: List[Tree.Case])(typeCheck: TypeCheck[A]): TypeCheck[A] =
              cases match {
                case Nil => typeCheck
                case Tree.Case(binder, body) :: cases =>
                  for {
                    _ <- bindTau(binder, Expectation.Check(tau0)) {
                      for {
                        tau <- inferTau(body)
                        _ <- TypeCheck.unify(tau1, tau)
                      } yield ()
                    }
                    result <- go(cases)(typeCheck)
                  } yield result
              }
  
            go(cases) {
              TypeCheck.unit
            }
          }
        } yield ()
        
      case Tree.Let(binder, definition, body) =>
        for {
          inference <- Expectation.empty[Type.Tau]
          
          tau <- bindTau(binder, inference) {
            for {
              tau0 <- inferTau(definition)
              tau1 <- inference.get
              _ <- TypeCheck.unify(tau1, tau0)
            } yield tau1
          }
          
          sigma <- TypeCheck.generalize(tau)
          _ <- bindSigma(binder, Expectation.Check(sigma)) {
            analyseTau(body, expectation)
          }
        } yield ()
  
      case Tree.Annotation(body, tau) =>
        for {
          sigma0 <- TypeCheck.generalize(tau)
          tau0 <- TypeCheck.skolemise(sigma0)
          tau1 <- inferTau(body)
          _ <- TypeCheck.unify(tau0, tau1)
          tau2 <- TypeCheck.instantiate(sigma0)
          _ <- fulfillTau(tau2, expectation)
        } yield ()
    }
  
  /**
   * Calls the provided `typeCheck` with the provided `binder` bound to a sigma type
   * @param binder The `binder`
   * @param expectation The expectation (i.e. either infer or check the sigma type of the binder)
   * @param typeCheck The `typeCheck`
   * @tparam A The result of the `typeCheck` itself
   * @return A type check that binds the `binder` with respect to the expectation and calls the
   *         provided `typeCheck` in this new environment
   */
  private def bindSigma[A](binder: Tree, expectation: Expectation[Type.Sigma])(typeCheck: TypeCheck[A]): TypeCheck[A] =
    binder match {
      case Tree.Variable(name) if name.headOption.exists(_.isUpper) =>
        for {
          sigma <- TypeCheck.lookup(name)
          tau <- TypeCheck.instantiate(sigma)
          _ <- fulfillSigma(tau, expectation)
          result <- typeCheck
        } yield result
  
      case Tree.Variable(name) =>
        for {
          tau <- TypeCheck.newMetaVariable
          _ <- fulfillSigma(tau, expectation)
          sigma <- TypeCheck.generalize(tau)
          result <- TypeCheck.enter(name, sigma)(typeCheck)
        } yield result
  
      case Tree.Application(function, argument) =>
        for {
          functionInference <- Expectation.empty[Type.Sigma]
          result <- bindSigma(function, functionInference) {
            for {
              sigma <- functionInference.get
              tau0 <- TypeCheck.instantiate(sigma)
          
              argumentInference <- Expectation.empty[Type.Sigma]
              result <- bindSigma(argument, argumentInference) {
                for {
                  sigma <- argumentInference.get
                  tau1 <- TypeCheck.instantiate(sigma)
              
                  tau <- TypeCheck.newMetaVariable
                  _ <- TypeCheck.unify(tau0, tau1 --> tau)
                  _ <- fulfillSigma(tau, expectation)
              
                  result <- typeCheck
                } yield result
              }
            } yield result
          }
        } yield result
  
      case Tree.Annotation(body, tau) =>
        for {
          result <- TypeCheck.skolemiseFreeVariables(tau) { tau0 =>
            for {
              _ <- fulfillSigma(tau0, expectation)
              sigma0 <- TypeCheck.generalize(tau0)
              result <- bindSigma(body, Expectation.Check(sigma0))(typeCheck)
            } yield result
          }
        } yield result
  
      case _ =>
        TypeCheck.fail(s"illegal pattern '$binder'")
    }
  
  /**
   * Calls the provided `typeCheck` with the provided `binder` bound to a tau type
   * @param binder The `binder`
   * @param expectation The expectation (i.e. either infer or check the tau type of the binder)
   * @param typeCheck The `typeCheck`
   * @tparam A The result of the `typeCheck` itself
   * @return A type check that binds the `binder` with respect to the expectation and calls the
   *         provided `typeCheck` in this new environment
   */
  private def bindTau[A](binder: Tree, expectation: Expectation[Type.Tau])(typeCheck: TypeCheck[A]): TypeCheck[A] = binder match {
    case Tree.Variable(name) if name.headOption.exists(_.isUpper) =>
      for {
        sigma <- TypeCheck.lookup(name)
        tau <- TypeCheck.instantiate(sigma)
        _ <- fulfillTau(tau, expectation)
        result <- typeCheck
      } yield result
      
    case Tree.Variable(name) =>
      for {
        tau <- TypeCheck.newMetaVariable
        _ <- fulfillTau(tau, expectation)
        result <- TypeCheck.enter(name, tau)(typeCheck)
      } yield result
    
    case Tree.Application(function, argument) =>
      for {
        functionInference <- Expectation.empty[Type.Tau]
        result <- bindTau(function, functionInference) {
          for {
            tau0 <- functionInference.get
            argumentInference <- Expectation.empty[Type.Tau]
            result <- bindTau(argument, argumentInference) {
              for {
                tau1 <- argumentInference.get
                tau <- TypeCheck.newMetaVariable
                _ <- TypeCheck.unify(tau0, tau1 --> tau)
                _ <- fulfillTau(tau, expectation)
                result <- typeCheck
              } yield result
            }
          } yield result
        }
      } yield result
    
    case Tree.Annotation(body, tau) =>
      for {
        result <- TypeCheck.skolemiseFreeVariables(tau) { tau0 =>
          for {
            _ <- fulfillTau(tau0, expectation)
            result <- bindTau(body, Expectation.Check(tau0))(typeCheck)
          } yield result
        }
      } yield result
      
    case _ =>
      TypeCheck.fail(s"illegal pattern '$binder'")
  }
  
}
