package model
import tableau.Axiom
import tableau.TBoxAxiom
import tableau.ABoxAxiom

class Ontology {
  var TBox : Set[TBoxAxiom] = Set[TBoxAxiom]()
  var ABox : Set[ABoxAxiom] = Set[ABoxAxiom]()
  
  def this (axioms: Set[Axiom]) = {
    this()
    for (axiom <- axioms){
      if (axiom.isInstanceOf[TBoxAxiom]) TBox += axiom.asInstanceOf[TBoxAxiom]
      else ABox += axiom.asInstanceOf[ABoxAxiom]
    }
  }
  
  def addAxiom (axiom: Axiom): Ontology = {
    if (axiom.isInstanceOf[TBoxAxiom]) TBox += axiom.asInstanceOf[TBoxAxiom]
    else ABox += axiom.asInstanceOf[ABoxAxiom]
    return this
  }
}