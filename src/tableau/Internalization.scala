package tableau

import Expr._

object Internalization {

  def internalize(axioms: Set[TBoxAxiom]): Expr = {

    val concepts = for (axiom ← axioms) yield {
      axiom.toConcept
    }

    val internalizedExpression = And(concepts.toList)

    return internalizedExpression
  }

}