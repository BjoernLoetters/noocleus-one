package noocleus.syntax

import cats.data.Validated
import cats.data.Validated.{Invalid, Valid}
import noocleus.semantic.Type

import scala.util.parsing.combinator.{ImplicitConversions, RegexParsers}

object Parser extends RegexParsers with ImplicitConversions {
  private lazy val keywords = Set(
    ":", ",", "=>", "(", ")", "->", "let", "=", "in", "data", "|", "match", "case", "{", "}"
  )
  
  def parse(content: String): Validated[String, Tree] =
    parseAll(tree, content) match {
      case Success(result, _) =>
        Valid(result)
      case NoSuccess(error, rest) =>
        Invalid(s"syntax error in line ${rest.pos.line} at column ${rest.pos.column}: $error\n${rest.pos.longString}")
    }
  
  private lazy val tree: Parser[Tree] = data | let | abstraction
  
  private lazy val let: Parser[Tree] =
    "let" ~> annotation ~ ("=" ~> tree) ~ ("in" ~> tree) ^^ Tree.Let
  
  private lazy val constructor: Parser[Tree.Constructor] =
    (name ^? ({
      case identifier if identifier.headOption.exists(_.isUpper) => identifier
    }, identifier => s"'$identifier' is not a valid constructor name")) ~ rep(simpleType) ^^ Tree.Constructor
  
  private lazy val data: Parser[Tree] =
    "data" ~> typeConstant ~ rep(typeVariable) ~ opt("=" ~> repsep(constructor, "|"))
      .map(_.getOrElse(List.empty[Tree.Constructor])) ~ ("in" ~> tree) ^^ Tree.Data
  
  private lazy val abstraction: Parser[Tree] =
    `match` ~ opt("=>" ~> tree) ^^ {
      case binder ~ body => body.foldLeft(binder)(Tree.Abstraction)
    }
  
  private lazy val `case`: Parser[Tree.Case] =
    "case" ~> annotation ~ ("=>" ~> tree) ^^ Tree.Case
  
  private lazy val `match`: Parser[Tree] =
    annotation ~ opt(("match" ~ "{") ~> rep(`case`) <~ "}") ^^ {
      case tree ~ cases => cases.foldLeft(tree)(Tree.Match)
    }
  
  private lazy val annotation: Parser[Tree] =
    application ~ opt(":" ~> tau) ^^ {
      case body ~ tau => tau.foldLeft(body)(Tree.Annotation)
    }
  
  private lazy val application: Parser[Tree] =
    rep1(value) ^^ (_.reduceLeft(Tree.Application))
  
  private lazy val value: Parser[Tree] =
    natural | tuple | variable
  
  private lazy val natural: Parser[Tree] =
    "[0-9]+".r.map(_.toInt) ^^ { n =>
      
      def natural(n: Int): Tree = n match {
        case 0 => Tree.Variable("Z")
        case n => Tree.Application(Tree.Variable("S"), natural(n - 1))
      }
      
      natural(n)
    }
  
  private lazy val tuple: Parser[Tree] =
    "(" ~> repsep(tree, ",") <~ ")" ^^ {
      case List(value) => value
      case values =>
        values.foldLeft[Tree](Tree.Variable("Tuple" + values.size))(Tree.Application)
    }
  
  private lazy val variable: Parser[Tree] =
    name ^^ Tree.Variable
  
  private lazy val tau: Parser[Type.Tau] = functionType
  
  private lazy val functionType: Parser[Type.Tau] =
    typeApplication ~ opt("->" ~> tau) ^^ {
      case domain ~ codomain => codomain.foldLeft(domain)(Type.Function)
    }
  
  private lazy val typeApplication: Parser[Type.Tau] =
    rep1(simpleType) ^^ (_.reduceLeft(Type.Application))
  
  private lazy val simpleType: Parser[Type.Tau] =
    tupleType | typeVariable | typeConstant
  
  private lazy val tupleType: Parser[Type.Tau] =
    "(" ~> repsep(tau, ",") <~ ")" ^^ {
      case List(value) => value
      case values =>
        values.foldLeft[Type.Tau](Type.Constant("Tuple" + values.size))(Type.Application)
    }
  
  private lazy val typeVariable: Parser[Type.Variable] =
    name ^? ({
      case identifier if !identifier.headOption.exists(_.isUpper) =>
        Type.Variable(identifier)
    }, identifier => s"'$identifier' is not a valid type variable")
  
  private lazy val typeConstant: Parser[Type.Constant] =
    name ^? ({
      case identifier if identifier.headOption.exists(_.isUpper) =>
        Type.Constant(identifier)
    }, identifier => s"'$identifier' is not a valid type constant")
  
  private lazy val name: Parser[String] = {
    "[a-zA-Z][a-zA-Z0-9]*'*".r | "(\\+|\\~|\\*|\\#|\\-|\\.|\\:|\\,|\\;|\\<|\\>|\\||\\@|\\^|\\!|\\$|\\%|\\&|\\/|\\?|\\\\|\\`|\\´|\\=)+".r
  } ^? ({
    case identifier if !(keywords contains identifier) => identifier
  }, identifier => s"'$identifier' is not a valid identifier")
  
}
