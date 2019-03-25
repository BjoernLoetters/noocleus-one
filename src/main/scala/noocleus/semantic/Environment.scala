package noocleus.semantic

case class Environment private(private val map: Map[String, Type]) {
  
  def this() = this(Map())
  
  def +(entry: (String, Type)): Environment =
    Environment(map + entry)
  
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
