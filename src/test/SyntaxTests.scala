package test
import org.junit._
import Assert._
import tableau._

class SyntaxTests {
  @Test def testAnd() {
    val expr1 = And(List(Concept("C"), Concept("D")))
    val expr2 = Concept("C") and Concept("D")
    assertEquals(expr1, expr2)
  }

}