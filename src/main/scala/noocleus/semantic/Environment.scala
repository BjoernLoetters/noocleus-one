package noocleus.semantic

import cats.effect.IO
import cats.effect.concurrent.Ref

case class Environment private(
  private val map: Map[String, Type],
  private val skolemised: Map[Type.Variable, Type.Variable],
  private val counter: Ref[IO, Int]
) {
  
  def this() = this(Map(), Map(), Ref.of[IO, Int](0).unsafeRunSync())
  
  def addSkolemisedVariable(variable: Type.Variable, skolemised: Type.Variable): Environment =
    Environment(map, this.skolemised + (variable -> skolemised), counter)
  
  def getSkolemisedVariable(variable: Type.Variable): Option[Type.Variable] =
    skolemised.get(variable)
  
  def nextId: IO[Int] =
    for {
      id <- counter.get
      _ <- counter.set(id + 1)
    } yield id
  
  def +(entry: (String, Type)): Environment =
    Environment(map + entry, skolemised, counter)
  
  def apply(name: String): Option[Type] =
    map.get(name)
  
  lazy val types: List[Type] = map.values.toList
  
  lazy val freeVariables: Set[Type.Variable] =
    types.map(_.freeVariables).toSet.flatten
  
  lazy val metaVariables: Set[Type.MetaVariable] =
    types.map(_.metaVariables).toSet.flatten
  
}

object Environment {
  
  def apply(): Environment =
    new Environment()
  
}
