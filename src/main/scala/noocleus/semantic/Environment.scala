package noocleus.semantic

case class Environment private(private val map: Map[String, Type], private val skolemised: Map[Type.Variable, Type.Variable]) {
  
  def this() = this(Map(), Map())
  
  def addSkolemisedVariable(variable: Type.Variable, skolemised: Type.Variable): Environment =
    Environment(map, this.skolemised + (variable -> skolemised))
  
  def getSkolemisedVariable(variable: Type.Variable): Option[Type.Variable] =
    skolemised.get(variable)
  
  def +(entry: (String, Type)): Environment =
    Environment(map + entry, skolemised)
  
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
