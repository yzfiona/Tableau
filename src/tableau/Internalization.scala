package tableau

import Expr._

object Internalization {

  def internalize(axioms: Set[Axiom]): Expr = {

    val concepts = for (axiom ← axioms) yield {
      axiom.toConcept
    }

    val internalizedExpression = And(concepts.toList)

    return internalizedExpression
  }

}