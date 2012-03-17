package test

import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import tableau.Internalization.internalize
import tableau._

class optimizedTableauTest {

  @Test def testModell1() {
    val expr: Expr =
      And(List(Concept("A"), ForAll(Role("R"), Not(Concept("A"))), Exists(Role("R"), Concept("B"))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    val result: Set[Set[Axiom]] = Set(Set(
      TypeAssertion(Ind("x1"), And(List(Concept("A"), ForAll(Role("R"), Not(Concept("A"))), Exists(Role("R"), Concept("B"))))),
      TypeAssertion(Ind("x1"), Concept("A")),
      TypeAssertion(Ind("x2"), Concept("B")),
      TypeAssertion(Ind("x2"), Not(Concept("A"))),
      RoleAssertion(Role("R"), Ind("x1"), Ind("x2")),
      TypeAssertion(Ind("x1"), ForAll(Role("R"), Not(Concept("A")))),
      TypeAssertion(Ind("x1"), Exists(Role("R"), Concept("B")))
    ))
    assertEquals(tableauR._2, result)
  }

  @Test def testModell2() {
    val expr: Expr =
      And(List(Concept("A"), Exists(Role("R"), Concept("A"))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    val result: Set[Set[Axiom]] = Set(Set(
      TypeAssertion(Ind("x1"), And(List(Concept("A"), Exists(Role("R"), Concept("A"))))),
      TypeAssertion(Ind("x1"), Concept("A")),
      TypeAssertion(Ind("x1"), Exists(Role("R"), Concept("A")))
    ))
    assertEquals(tableauR._2, result)
  }

  @Test def testModell3() {
    val expr: Expr =
      And(List(Concept("A"), Or(List(Concept("A"), And(List(Not(Concept("A")), Concept("C")))))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    val result: Set[Set[Axiom]] = Set(Set(
      TypeAssertion(Ind("x1"), And(List(Concept("A"), Or(List(Concept("A"), And(List(Not(Concept("A")), Concept("C")))))))),
      TypeAssertion(Ind("x1"), Concept("A")),
      TypeAssertion(Ind("x1"), Or(List(Concept("A"), And(List(Not(Concept("A")), Concept("C"))))))
    ))
    assertEquals(tableauR._2, result)
  }

  @Test def testBlocking() {
    val expr: Expr =
      And(List(Concept("A"), ForAll(Role("R"), Not(Concept("A"))), Exists(Role("R"), Concept("A"))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    assertTrue(tableauR._1)
  }

  @Test def testclash() {
    val expr: Expr =
      And(List(Exists(Role("R"), Concept("A")), Exists(Role("R"), Concept("B")), Not(Exists(Role("R"), And(List(Concept("A"), Concept("B")))))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    assertTrue(tableauR._1)
  }

  @Test def testOr() {
    val expr: Expr =
      And(List(Concept("A"), Or(List(Not(Concept("A")), And(List(Concept("A"), Or(List(Not(Concept("A")), Concept("C")))))))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    val result: Set[Set[Axiom]] = Set(Set(
      TypeAssertion(Ind("x1"), And(List(Concept("A"), Or(List(Not(Concept("A")), And(List(Concept("A"), Or(List(Not(Concept("A")), Concept("C")))))))))),
      TypeAssertion(Ind("x1"), Concept("A")),
      TypeAssertion(Ind("x1"), Or(List(Not(Concept("A")), And(List(Concept("A"), Or(List(Not(Concept("A")), Concept("C")))))))),
      TypeAssertion(Ind("x1"), And(List(Concept("A"), Or(List(Not(Concept("A")), Concept("C")))))),
      TypeAssertion(Ind("x1"), Or(List(Not(Concept("A")), Concept("C")))),
      TypeAssertion(Ind("x1"), Concept("C"))
    ))
    assertEquals(tableauR._2, result)
  }

  @Test def testnestedAnd() {
    val expr: Expr =
      Not(Not(And(List(Concept("A"), Concept("B"), And(List(Not(Or(List(Concept("A"), Concept("D")))), Concept("E")))))))
    val tableauR = new OptimizedTableau().isSatisfiable(expr)
    assertTrue(tableauR._1)
  }

  @Test def testTime() {
    val expr: Expr =
      And(List(Exists(Role("R"), Concept("A")), Exists(Role("R"), Concept("B")), Exists(Role("R"), Concept("C")),
        Exists(Role("R"), Concept("D")), Exists(Role("R"), Concept("E")), Exists(Role("R"), Concept("F")),
        Exists(Role("R"), Concept("G")), Exists(Role("R"), Concept("H")), Exists(Role("R"), Concept("I")),
        Exists(Role("R"), Concept("J")), Exists(Role("R"), Concept("K")), Exists(Role("R"), Concept("L")),
        Exists(Role("R"), Concept("M")), Exists(Role("R"), Concept("N")), Exists(Role("R"), Concept("O")),
        Exists(Role("R"), Concept("P")), Exists(Role("R"), Concept("Q")), Exists(Role("R"), Concept("R")),
        Exists(Role("R"), Concept("S")), Exists(Role("T"), Concept("U")), Exists(Role("R"), Concept("V")),
        Exists(Role("R"), Concept("W")), Exists(Role("R"), Concept("X")), Exists(Role("R"), Concept("Y")),
        Exists(Role("R"), Concept("Z")),
        Not(Exists(Role("R"), And(List(Concept("A"), Concept("B")))))))
    val start = System.currentTimeMillis()
    for (i ← 1 to 100)
      new OptimizedTableau().isSatisfiable(expr)

    val end = System.currentTimeMillis()
    println("Execution Time:" + ((end - start) / 100) + "ms");
    assertTrue(true)
  }
  
  @Test def testInternalization1() {
    val onto : Set[Axiom] = Set(SubClassOf(Concept("a"), Concept("b")), SubClassOf(Concept("b"), Concept("c")))
    val axiom  = SubClassOf(Concept("a"), Concept("c"))
    val tableauR = new OptimizedTableau().isSatisfiable(axiom, onto)
    assertTrue(tableauR._1)
  }

  @Test def testInternalization2() {
    val onto : Set[Axiom] = Set(SubClassOf(Concept("a"), Concept("b")), SubClassOf(Concept("b"), Concept("a")))
    val axiom  = EquivalentClass(Concept("a"), Concept("b"))
    val tableauR = new OptimizedTableau().isSatisfiable(axiom, onto)
    assertTrue(tableauR._1)
  }
  
    
   @Test def testmaxCardinality() {
    val onto : Set[Axiom] = Set(EquivalentClass(Concept("Job1"), Not(Concept("Job2"))))
    val axiom  = maxCardinality(1, Role("hatVollZeitJob")) and Exists(Role("hatVollZeitJob"), Concept("Job1")) and Exists(Role("hatVollZeitJob"), Concept("Job2"))
    val tableauR = new OptimizedTableau().isSatisfiable(internalize(onto) and axiom)
    assertTrue(tableauR._1)
  }
  
}