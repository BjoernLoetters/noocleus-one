package noocleus.semantic

import cats.effect.IO
import cats.effect.concurrent.Ref
import org.typelevel.paiges.Doc

sealed trait Type extends Product with Serializable {
  
  def substitute(variable: Type.Variable, tau: Type.Tau): Type
  
  def substituteMetaVariable(variable: Type.MetaVariable, tau: Type.Tau): Type
  
  final def substitute(theta: Map[Type.Variable, Type.Tau]): Type =
    theta.foldLeft(this) { case (previous, (variable, tau)) =>
      previous.substitute(variable, tau)
    }
  
  final def substituteMetaVariables(theta: Map[Type.MetaVariable, Type.Tau]): Type =
    theta.foldLeft(this) { case (previous, (variable, tau)) =>
      previous.substituteMetaVariable(variable, tau)
    }
  
  def binders: Set[Type.Variable]
  
  def freeVariables: Set[Type.Variable]
  
  def metaVariables: Set[Type.MetaVariable]
  
  def skolemisedVariables: Set[Type.Variable]
  
  def doc: Doc
  
  final def -->(codomain: Type.Tau): Type.Tau =
    Type.Function(this, codomain)
  
  override final def toString: String =
    doc.render(80)
  
}

object Type {
  
  type Sigma = Type
  type Tau = Type
  
  case class Constant(name: String) extends Type.Tau {
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      this
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      this
    
    lazy val binders: Set[Type.Variable] = Set()
    
    lazy val freeVariables: Set[Type.Variable] = Set()
  
    lazy val skolemisedVariables: Set[Type.Variable] = Set()
    
    lazy val metaVariables: Set[Type.MetaVariable] = Set()
    
    lazy val doc: Doc = Doc.text(name)
    
  }
  
  sealed trait Variable extends Type.Tau {
    
    def name: String
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      if (this == variable) tau
      else this
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      this
  
    lazy val binders: Set[Type.Variable] = Set()
  
    lazy val freeVariables: Set[Type.Variable] = Set(this)
  
    lazy val metaVariables: Set[Type.MetaVariable] = Set()
  
    lazy val doc: Doc = Doc.text(name)
    
  }
  
  object Variable {
    
    case class Skolemised(name: String) extends Variable {
  
      override def equals(any: Any): Boolean = any match {
        case skolemised: Skolemised => this eq skolemised
        case _ => false
      }
  
      override def hashCode(): Int = System.identityHashCode(this)
  
      lazy val skolemisedVariables: Set[Type.Variable] = Set(this)
      
    }
    
    case class Bound(name: String) extends Variable {
      
      lazy val skolemisedVariables: Set[Type.Variable] = Set()
      
    }
    
  }
  
  private lazy val greekLetters = ('\u03b1' to '\u03c9').map(_.toString).toArray
  
  case class MetaVariable(id: Int, instance: Ref[IO, Option[Type.Tau]]) extends Type.Tau {
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      this
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      if (this == variable) tau
      else this
  
    lazy val binders: Set[Type.Variable] = Set()
    
    lazy val freeVariables: Set[Type.Variable] = Set()
  
    lazy val skolemisedVariables: Set[Type.Variable] = Set()
    
    lazy val metaVariables: Set[Type.MetaVariable] = Set(this)
   
    lazy val doc: Doc = Doc.text(greekLetters(id % greekLetters.length) + (id / greekLetters.length))
    
    override def equals(any: Any): Boolean = any match {
      case variable: MetaVariable => variable.instance eq instance
      case _ => false
    }
  
    override def hashCode(): Int = System.identityHashCode(instance)
    
  }
  
  case class Application(function: Type.Tau, argument: Type.Tau) extends Type.Tau {
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      Application(function.substitute(variable, tau), argument.substitute(variable, tau))
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      Application(function.substituteMetaVariable(variable, tau), argument.substituteMetaVariable(variable, tau))
  
    lazy val binders: Set[Type.Variable] =
      function.binders ++ argument.binders
    
    lazy val freeVariables: Set[Type.Variable] =
      function.freeVariables ++ argument.freeVariables
  
    lazy val skolemisedVariables: Set[Type.Variable] =
      function.skolemisedVariables ++ argument.skolemisedVariables
    
    lazy val metaVariables: Set[Type.MetaVariable] =
      function.metaVariables ++ argument.metaVariables
    
    lazy val doc: Doc = (function, argument) match {
      case (_: Function | _: ForAll, _: Application | _: Function | _: ForAll) =>
        Doc.char('(') + function.doc + Doc.char(')') + Doc.space + Doc.char('(') + argument.doc + Doc.char(')')
      case (_: Function | _: ForAll, _) =>
        Doc.char('(') + function.doc + Doc.char(')') + Doc.space + argument.doc
      case (_, _: Application | _: Function | _: ForAll) =>
        function.doc + Doc.space + Doc.char('(') + argument.doc + Doc.char(')')
      case (_, _) =>
        function.doc + Doc.space + argument.doc
    }
    
  }
  
  case class Function(domain: Type.Tau, codomain: Type.Tau) extends Type.Tau {
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      Function(domain.substitute(variable, tau), codomain.substitute(variable, tau))
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      Function(domain.substituteMetaVariable(variable, tau), codomain.substituteMetaVariable(variable, tau))
  
    lazy val binders: Set[Type.Variable] =
      domain.binders ++ codomain.binders
    
    lazy val freeVariables: Set[Type.Variable] =
      domain.freeVariables ++ codomain.freeVariables
  
    lazy val skolemisedVariables: Set[Type.Variable] =
      domain.skolemisedVariables ++ codomain.skolemisedVariables
    
    lazy val metaVariables: Set[Type.MetaVariable] =
      domain.metaVariables ++ codomain.metaVariables
    
    lazy val doc: Doc = domain match {
      case _: Function | _: ForAll =>
        Doc.char('(') + domain.doc + Doc.char(')') + Doc.space + Doc.text("->") + Doc.space + codomain.doc
      case _ =>
        domain.doc + Doc.space + Doc.text("->") + Doc.space + codomain.doc
    }
    
  }
  
  case class ForAll(variables: List[Type.Variable], tau: Type.Tau) extends Type.Sigma {
  
    override def substitute(variable: Variable, tau: Type.Tau): Type =
      if (variables.contains(variable)) this
      else ForAll(variables, this.tau.substitute(variable, tau))
  
    override def substituteMetaVariable(variable: MetaVariable, tau: Type.Tau): Type =
      ForAll(variables, this.tau.substituteMetaVariable(variable, tau))
    
    lazy val binders: Set[Type.Variable] =
      variables.toSet
    
    lazy val freeVariables: Set[Type.Variable] =
      tau.freeVariables -- variables
  
    lazy val skolemisedVariables: Set[Type.Variable] =
      tau.skolemisedVariables
    
    lazy val metaVariables: Set[Type.MetaVariable] =
      tau.metaVariables
    
    lazy val doc: Doc =
      Doc.text("forall") + Doc.space + Doc.intercalate(Doc.space, variables.map(_.doc)) + Doc.space +
        Doc.char('.') + Doc.space + tau.doc
    
  }
  
}
