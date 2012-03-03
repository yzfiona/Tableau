package tableau
import Expr._

/** ALC Expressions
  */

object Expr {
  def ⊥ = Bottom
  def ⊤ = Top
  def ¬(c: Expr) = Not(c)
  def ∃(r: Role, c: Expr) = Exists(r, c)
  def ∀(r: Role, c: Expr): Expr = ForAll(r, c)
}

abstract class Expr {
  def and(c: Expr): Expr = And(List(this, c))
  def or(c: Expr): Expr = And(List(this, c))
  def ⊓(c: Expr): Expr = and(c)
  def ⊔(c: Expr): Expr = or(c)
  def ≤(n: Integer, r: Role, f: Expr): Expr = maxCardinality(n: Integer, r: Role, f: Expr)
  def ≥(n: Integer, r: Role, f: Expr): Expr = minCardinality(n: Integer, r: Role, f: Expr)
}

case object Top extends Expr
case object Bottom extends Expr
case class Concept(c: String) extends Expr
case class Not(c: Expr) extends Expr
case class And(f: List[Expr]) extends Expr
case class Or(f: List[Expr]) extends Expr
case class Exists(r: Role, f: Expr) extends Expr
case class ForAll(r: Role, f: Expr) extends Expr
case class maxCardinality(n: Integer, r: Role, f: Expr) extends Expr
case class minCardinality(n: Integer, r: Role, f: Expr) extends Expr

abstract class Individual
case class Ind(a: String) extends Individual
case class BNode(a: String) extends Individual

abstract class RoleExpr extends Expr
case class Role(r: String) extends RoleExpr
//case class InvRole(r: Role) extends RoleExpr

abstract class Axiom {
  def toConcept: Expr
}
case class TypeAssertion(a: Ind, expr: Expr) extends Axiom {
  def toConcept = ⊥ // FIXME find other solution (use nominals?)
}
case class RoleAssertion(r: Role, a: Ind, b: Ind) extends Axiom {
  def toConcept = ⊥ // FIXME find other solution (use nominals?)
}
case class SubClassOf(c: Expr, d: Expr) extends Axiom {
  def toConcept = ¬(c) ⊔ d
}
case class EquivalentClass(c: Expr, d: Expr) extends Axiom {
  def toConcept = (¬(c) ⊔ d) ⊓ (c ⊔ ¬(d))
}

//case class InvRoleAssertion(r: Role, s: Role) extends RoleExpr

/** ALC Interpretation
  */

class AtomicConcepts[A](concepts: List[(Concept, Set[A])])
class AtomicRoles[A](roles: List[(Role, Set[(A, A)])])

class TInterpretation[A](domain: Set[A], concepts: AtomicConcepts[A], roles: AtomicRoles[A]) {
  // FIXME 
  //def iC :: TInterpretation a -> AtomicConcept 
  //: Set[A]
  // iC (_,acs,_) cn = maybe Set.empty id $ lookup cn acs
  //
  //def iR :: TInterpretation a -> AtomicRole 
  //: Set[Pair[A,A]]
  //
  //     iR (_,_,ars) rn = maybe Set.empty id $ lookup rn ars
}
