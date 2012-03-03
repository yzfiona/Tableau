package tableau

/**
 * regular expressions
 */

abstract class RegExp
case object EmptySet extends RegExp
case object EmptyString extends RegExp
case class Literal(x: String) extends RegExp
case class Conc(xs: List[RegExp]) extends RegExp
case class Choice(xs: List[RegExp]) extends RegExp
case class Star(x: RegExp) extends RegExp
