package tableau

/**
 * TODO ALC+regular Expressions
 */
abstract class ALCregExpr extends Expr
case class RegExConcept(reg: RegExp) extends ALCregExpr

