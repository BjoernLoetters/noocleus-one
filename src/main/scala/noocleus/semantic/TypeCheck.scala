package noocleus.semantic

import cats.Monad
import cats.data.Validated
import cats.data.Validated.{Invalid, Valid}
import cats.effect.IO
import cats.effect.concurrent.Ref
import cats.implicits._

sealed trait TypeCheck[+A] extends (Environment => IO[Validated[String, A]]) {
  
  def withFilter(predicate: A => Boolean): TypeCheck[A] =
    for {
      value <- this
      result <-
        if (predicate(value)) TypeCheck.pure(value)
        else TypeCheck.fail(s"predicate not fulfilled for value '$value'")
    } yield result
  
}

object TypeCheck {
  
  /**
   * Unifies the two tau types, i.e. instantiates meta variables in both types
   * until they are equivalent or fails, if they can not be unified.
   * @param a The first tau type
   * @param b The second tau type
   * @return This function returns nothing (except the enclosing type check monad)
   *         since the unification instantiates meta variables as a side effect.
   */
  def unify(a: Type.Tau, b: Type.Tau): TypeCheck[Unit] = {
    
    def typeMismatch(a1: Type.Tau, b1: Type.Tau): TypeCheck[Unit] =
      for {
        a0 <- zonk(a)
        b0 <- zonk(b)
        morePrecisely =
          if (a0 != a1 || b0 != b1)
            s"""
               |
               |more precisely between type
               |  `$a1`
               |and type
               |  `$b1`""".stripMargin
          else s""
        // skolemised variables always arise from user supplied type variables
        rigidTypeVariables = (a1.skolemisedVariables ++ b1.skolemisedVariables).toList
        where = rigidTypeVariables match {
          case Nil => ""
          case List(single) =>
            s"""
               |
               |where `$single` is a rigid type variable""".stripMargin
          case init :+ last =>
            s"""
               |
               |where ${init.map("`" + _ + "`").mkString(", ")} and `$last` are rigid type variables""".stripMargin
        }
        _ <- TypeCheck.fail[Unit](
          s"""type mismatch between type
           |  `$a0`
           |and type
           |  `$b0`$morePrecisely$where""".stripMargin)
      } yield ()
      
    def unifyUnboundVariable(variable: Type.MetaVariable, tau: Type.Tau): TypeCheck[Unit] =
      tau match {
        case tau: Type.MetaVariable =>
          for {
            instance <- TypeCheck.readMetaVariable(tau)
            _ <- instance.map(go(variable, _)).getOrElse(TypeCheck.writeMetaVariable(variable, tau))
          } yield ()
          
        case tau if tau.metaVariables.contains(variable) =>
          TypeCheck.fail(s"recursive type when unifying '$tau' with $variable")
          
        case tau =>
          TypeCheck.writeMetaVariable(variable, tau)
      }
    
    def unifyVariable(variable: Type.MetaVariable, tau: Type.Tau): TypeCheck[Unit] =
      for {
        instance <- TypeCheck.readMetaVariable(variable)
        _ <- instance.map(go(_, tau)).getOrElse(unifyUnboundVariable(variable, tau))
      } yield ()
    
    def go(a: Type.Tau, b: Type.Tau): TypeCheck[Unit] =
      zonk(a).flatMap(a => zonk(b).map((a, _)).flatMap {
        case (a: Type.Variable, b: Type.Variable) if a == b =>
          TypeCheck.unit
          
        case (a: Type.MetaVariable, b: Type.MetaVariable) if a == b =>
          TypeCheck.unit
          
        case (a: Type.Constant, b: Type.Constant) if a == b =>
          TypeCheck.unit
          
        case (a: Type.MetaVariable, b) =>
          unifyVariable(a, b)
          
        case (a, b: Type.MetaVariable) =>
          unifyVariable(b, a)
          
        case (Type.Function(domain0, codomain0), Type.Function(domain1, codomain1)) =>
          for {
            _ <- go(domain0, domain1)
            _ <- go(codomain0, codomain1)
          } yield ()

        case (Type.Application(function0, argument0), Type.Application(function1, argument1)) =>
          for {
            _ <- go(function0, function1)
            _ <- go(argument0, argument1)
          } yield ()

        case (a, b) =>
          typeMismatch(a, b)
      })
    
    go(a, b)
  }
  
  /**
   * A infinite stream of binders (i.e. type variables) following the
   * scheme 'a0', 'b0', ... 'z0', 'a1', 'b1', ...
   */
  lazy val allBinders: Stream[Type.Variable] = {
    def go(id: Int): Stream[Type.Variable] =
      ('a' to 'z').toStream.map(_.toString + id).map(Type.Variable.Bound) #::: go(id + 1)
    go(0)
  }
  
  /**
   * Replaces all instantiated meta variables by their instances. As
   * a side effect all instantiated meta variables will be "shorted
   * out" (i.e. the instance is replaced by its zonked version)
   * @param tau The type that should be zonked out
   * @return A tau type that is equivalent to the provided one but
   *         with all instantiated meta variables replaced by their
   *         instances
   */
  def zonk(tau: Type.Tau): TypeCheck[Type.Tau] =
    tau match {
      case variable: Type.MetaVariable =>
        TypeCheck.readMetaVariable(variable).flatMap {
          case Some(tau) =>
            for {
              zonked <- zonk(tau)
              _ <- TypeCheck.writeMetaVariable(variable, zonked)
            } yield zonked
          case None => TypeCheck.pure(variable)
        }
    
      case Type.Application(function, argument) =>
        for {
          z0 <- zonk(function)
          z1 <- zonk(argument)
        } yield Type.Application(z0, z1)
    
      case Type.Function(domain, codomain) =>
        for {
          z0 <- zonk(domain)
          z1 <- zonk(codomain)
        } yield Type.Function(z0, z1)
    
      case Type.ForAll(variables, tau) =>
        zonk(tau).map(Type.ForAll(variables, _))
    
      case _ => TypeCheck.pure(tau)
    }
  
  /**
   * Generalizes the monomorphic type `tau` by closing over all free type
   * variables (and meta type variables)
   * @param tau The monomorphic `tau` type
   * @return A generalization of the monomorphic type `tau` (all free type
   *         variables and all meta type variables that are not bound by
   *         the current environment will be bound by an universal quantifier)
   */
  def generalize(tau: Type.Tau): TypeCheck[Type.Sigma] =
    for {
      tau0 <- zonk(tau)
      environment <- TypeCheck.environment
      zonked <- environment.metaVariables.toList
        .flatTraverse[TypeCheck, Type.MetaVariable](zonk(_).map(_.metaVariables.toList))
      
      metaVariables = (tau0.metaVariables -- zonked).toList
      unboundVariables = tau0.freeVariables -- environment.freeVariables
      
      newBinders = allBinders
        .filterNot(tau0.freeVariables.contains)
        .filterNot(tau0.binders.contains)
        .take(metaVariables.size + unboundVariables.size)
        .toList
      
      metaVariableSubstitution = metaVariables.zip(newBinders).toMap
      typeVariableSubstitution = unboundVariables.zip(newBinders.drop(metaVariables.size)).toMap
      
      substituted = tau0
        .substituteMetaVariables(metaVariableSubstitution)
        .substitute(typeVariableSubstitution)
      sigma = if (newBinders.isEmpty) substituted else Type.ForAll(newBinders, substituted)
    } yield sigma
  
  /**
   * Specialize the polymorphic type `sigma` by replacing all bound type variables
   * with meta-variables (i.e. monomorphic types)
   * @param sigma The polymorphic type `sigma`
   * @return An instantiation of the polymorphic type `sigma`
   */
  def instantiate(sigma: Type.Sigma): TypeCheck[Type.Tau] = sigma match {
    case Type.ForAll(variables, tau) =>
      variables
        .traverse[TypeCheck, (Type.Variable, Type.Tau)](variable => newMetaVariable.map(variable -> _))
        .map(_.toMap)
        .map(tau.substitute)
    
    case _ =>
      TypeCheck.pure(sigma)
  }
  
  /**
   * Skolemises all free type variables in the tau type and runs the
   * provided type check (remembering the skolemised variables for
   * future use in the environment)
   * @param tau The tau type
   * @param typeCheck The type check
   * @tparam A The result of the type check
   * @return The type check
   */
  def skolemiseFreeVariables[A](tau: Type.Tau)(typeCheck: Type.Tau => TypeCheck[A]): TypeCheck[A] = {
    
    def go[A](tau: Type.Tau)(typeCheck: Type.Tau => TypeCheck[A]): TypeCheck[A] = tau match {
      case variable: Type.Variable =>
        for {
          environment <- TypeCheck.environment
          result <-
            if ((variable.freeVariables -- environment.freeVariables).contains(variable))
              environment.getSkolemisedVariable(variable) match {
                case Some(skolemised) => typeCheck(skolemised)
                case None =>
                  val skolemised = Type.Variable.Skolemised(variable.name)
                  TypeCheck.modify(_.addSkolemisedVariable(variable, skolemised))(typeCheck(skolemised))
              }
            else typeCheck(variable)
        } yield result

      case Type.Application(function, argument) =>
        go(function)(function => go(argument)(argument => typeCheck(Type.Application(function, argument))))
        
      case Type.Function(domain, codomain) =>
        go(domain)(domain => go(codomain)(codomain => typeCheck(Type.Function(domain, codomain))))
      
      case _ =>
        typeCheck(tau)
    }
    
    go(tau)(typeCheck)
  }
  
  /**
   * Skolemises all type variables that are quantified by the outermost forall
   * of the provided sigma type
   * @param sigma The sigma type
   * @return A skolemised version of `sigma`
   */
  def skolemise(sigma: Type.Sigma): TypeCheck[Type.Tau] = sigma match {
    case Type.ForAll(variables, tau) =>
      val substitution = variables
        .map(variable => variable -> Type.Variable.Skolemised(variable.name))
        .toMap
      
      TypeCheck.pure(tau.substitute(substitution))
      
    case _ =>
      TypeCheck.pure(sigma)
  }
  
  /** A type check that simply returns unit */
  lazy val unit: TypeCheck[Unit] = TypeCheck.pure(())
  
  /** Calls the provided typeCheck with a modified version of the environment */
  def modify[A](f: Environment => Environment)(typeCheck: TypeCheck[A]): TypeCheck[A] =
    TypeCheck(environment => typeCheck(f(environment)))
  
  /** Calls the provided typeCheck with `name` and `type` entered in the environment */
  def enter[A](name: String, `type`: Type)(typeCheck: TypeCheck[A]): TypeCheck[A] =
    modify(_ + (name -> `type`))(typeCheck)
  
  /** A type check that returns the current environment*/
  def environment: TypeCheck[Environment] =
    TypeCheck(environment => IO.pure(Valid(environment)))
  
  /** Creates a new (uninstantiated) meta variable */
  def newMetaVariable: TypeCheck[Type.MetaVariable] =
    for {
      environment <- TypeCheck.environment
      id <- TypeCheck.lift(environment.nextId)
      variable <- TypeCheck.lift(Ref.of[IO, Option[Type.Tau]](None)).map(Type.MetaVariable(id, _))
    } yield variable
    
  
  /** Reads the value of a meta variable */
  def readMetaVariable(variable: Type.MetaVariable): TypeCheck[Option[Type.Tau]] =
    TypeCheck.lift(variable.instance.get)
  
  /** Writes a meta variable */
  def writeMetaVariable(variable: Type.MetaVariable, tau: Type.Tau): TypeCheck[Unit] =
    TypeCheck.lift(variable.instance.set(Some(tau)))
  
  /** Lifts an IO action into a type check */
  def lift[A](io: IO[A]): TypeCheck[A] =
    TypeCheck(_ => io.map(Valid(_)))
  
  /** Constructor for a type check */
  def apply[A](f: Environment => IO[Validated[String, A]]): TypeCheck[A] =
    new TypeCheck[A] { def apply(environment: Environment): IO[Validated[String, A]] = f(environment) }

  /** Returns a type check that will always fail with the provided message */
  def fail[A](message: String): TypeCheck[A] =
    TypeCheck(_ => IO.pure(Invalid(message)))
  
  /** Returns a type check that will print the provided message */
  def println(any: Any): TypeCheck[Unit] =
    TypeCheck.lift(IO(Predef.println(any)))
  
  private lazy val TupleConstructor = "Tuple([0-9]+)".r
  
  /** Returns a type check that will fetch the sigma type of the provided variable */
  def lookup(name: String): TypeCheck[Type.Sigma] = name match {
    case TupleConstructor(n) =>
      val binders = allBinders.take(n.toInt).toList
      val tupleType = binders.foldLeft[Type](Type.Constant("Tuple" + n.toInt))(Type.Application)
      val resultType = Type.ForAll(binders, binders.foldRight[Type](tupleType) {
        case (next, previous) => next --> previous
      })
      TypeCheck.pure(resultType)
    case _ =>
      TypeCheck.environment.flatMap(_(name) match {
        case Some(sigma) => TypeCheck.pure(sigma)
        case None => TypeCheck.fail(s"unknown variable '$name'")
      })
  }
  
  /** Returns a type check that will always yield the provided value */
  def pure[A](value: A): TypeCheck[A] =
    TypeCheck(_ => IO.pure(Valid(value)))
  
  implicit val monadInstance: Monad[TypeCheck] = new Monad[TypeCheck] {
    
    def flatMap[A, B](typeCheck: TypeCheck[A])(f: A => TypeCheck[B]): TypeCheck[B] =
      TypeCheck { environment =>
        typeCheck(environment).flatMap {
          case Valid(value) => f(value)(environment)
          case Invalid(error) => IO.pure(Invalid(error))
        }
      }
  
    def tailRecM[A, B](start: A)(f: A => TypeCheck[Either[A, B]]): TypeCheck[B] =
      TypeCheck { environment =>
        IO {
          var current: Validated[String, Either[A, B]] = f(start)(environment).unsafeRunSync()
          
          while (current.exists(_.isLeft)) {
            current = f(current.toEither.right.get.left.get)(environment).unsafeRunSync()
          }
          
          current.map(_.right.get)
        }
      }
  
    def pure[A](value: A): TypeCheck[A] =
      TypeCheck.pure(value)
    
  }

}
