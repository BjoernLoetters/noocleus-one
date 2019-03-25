package noocleus.syntax

import noocleus.semantic.Type
import org.typelevel.paiges.Doc

sealed trait Tree extends Product with Serializable {
  
  def doc: Doc
  
  final override def toString: String =
    doc.render(80)
  
}

object Tree {
  
  case class Variable(name: String) extends Tree {
    
    lazy val doc: Doc = Doc.text(name)
    
  }
  
  case class Application(function: Tree, argument: Tree) extends Tree {
    
    lazy val doc: Doc = (function, argument) match {
      case (_: Abstraction | _: Let, _: Application | _: Abstraction | _: Let) =>
        Doc.char('(') + function.doc + Doc.char(')') + Doc.space + Doc.char('(') + argument.doc + Doc.char(')')
      case (_, _: Application | _: Abstraction | _: Let) =>
        function.doc + Doc.space + Doc.char('(') + argument.doc + Doc.char(')')
      case (_: Abstraction | _: Let, _) =>
        Doc.char('(') + function.doc + Doc.char(')') + Doc.space + argument.doc
      case (_, _) =>
        function.doc + Doc.space + argument.doc
    }
    
  }
  
  case class Abstraction(binder: Tree, body: Tree) extends Tree {
    
    lazy val doc: Doc = binder.doc + Doc.space + Doc.text("=>") + Doc.space + body.doc
    
  }
  
  case class Annotation(body: Tree, `type`: Type.Tau) extends Tree {
    
    lazy val doc: Doc = body match {
      case _: Abstraction | _: Annotation | _: Let =>
        Doc.char('(') + body.doc + Doc.char(')') + Doc.char(':') + Doc.space + `type`.doc
      case _ =>
        body.doc + Doc.char(':') + Doc.space + `type`.doc
    }
    
  }
  
  case class Let(binder: Tree, definition: Tree, body: Tree) extends Tree {
    
    lazy val doc: Doc =
      Doc.text("let") + Doc.space + binder.doc + Doc.space + Doc.char('=') + Doc.space +
        definition.doc + Doc.space + Doc.text("in") + Doc.space + body.doc
    
  }
  
  case class Case(binder: Tree, body: Tree) {
    
    lazy val doc: Doc =
      Doc.text("case") + Doc.space + binder.doc + Doc.space + Doc.text("=>") + Doc.space + body.doc
    
  }
  
  case class Match(tree: Tree, cases: List[Case]) extends Tree {
    
    lazy val doc: Doc =
      tree.doc + Doc.space + Doc.text("match") + Doc.space + Doc.char('{') + Doc.lineBreak + Doc.intercalate(Doc.lineBreak + Doc.space + Doc.space, cases.map(_.doc)) + Doc.lineBreak + Doc.char('}')
    
  }
  
  case class Constructor(name: String, parameters: List[Type.Tau]) {
    
    lazy val doc: Doc =
      Doc.text(name) + Doc.space + Doc.intercalate(Doc.space, parameters.map(_.doc))
    
  }
  
  case class Data(
     typeName: Type.Constant,
     typeParameters: List[Type.Variable],
     constructors: List[Constructor],
     body: Tree
  ) extends Tree {
    
    lazy val doc: Doc =
      Doc.text("data") + Doc.space + typeName.doc + Doc.space + Doc.intercalate(Doc.space, typeParameters.map(_.doc)) +
        Doc.space + Doc.char('=') + Doc.space + Doc.intercalate(Doc.space + Doc.char('|') + Doc.space, constructors.map(_.doc)) +
        Doc.space + Doc.text("in") + Doc.space + body.doc
    
  }
  
}
