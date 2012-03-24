package tableau

object NNF {

  def nnf(expr: Expr): Expr = expr match {
    case Concept(c) => Concept(c)
    case Not(Not(c)) => nnf(c)
    case Not(Concept(c)) => Not(Concept(c))

    case And(cs) => And(cs.map(nnf))
    case Not(And(cs)) => Or(cs.map(Not andThen nnf))

    case Or(cs) => Or(cs.map(nnf))
    case Not(Or(cs)) => And(cs.map(Not andThen nnf))

    case ForAll(r, c) => ForAll(r, nnf(c))
    case Not(ForAll(r, c)) => Exists(r, nnf(Not(c)))

    case Exists(r, c) => Exists(r, nnf(c))
    case Not(Exists(r, c)) => ForAll(r, nnf(Not(c)))
    
    case maxCardinality(n, r) => maxCardinality(n, r)
    case Not(maxCardinality(n, r)) => minCardinality(n+1, r)
    
    case minCardinality(n, r) => 
      if (n >= 1) minCardinality(n, r)
      else if (n == 0) Top
      else {println("[ERROR] untreated: " + expr); null}
    case Not(minCardinality(n, r)) => 
      if (n >= 1) maxCardinality(n-1, r)
      else if (n == 0) Bottom
      else {println("[ERROR] untreated: " + expr); null}  

    case _ => {println("[ERROR] untreated: " + expr); null}
  }

  def main(args: Array[String]): Unit = {
    println(nnf(Not(And(List(Concept("Person"), Concept("Parent"), ForAll(Role("hasChild"), And(List(Concept("Lawyer"), Concept("Doctor"), Concept("Rockstar")))))))))
    println(nnf(Not(Not(And(List(Concept("A"), Concept("B"), Not(Or(List(Concept("C"), Concept("D"), Concept("E"))))))))))
  }

}
