package tableau;

import NNF.nnf
import tableau.Internalization.internalize
import model.OntologySpec._

class OptimizedTableau {

  private var counter: Int = 0;
  private def nextInd(): Ind = { counter += 1; return Ind("x" + counter) }

  private var clash: Boolean = false
  private var model = Set[Set[Axiom]]()
  private var newSet: Map[Axiom, Boolean] = Map()

  var instanceSet: Set[Ind] = Set[Ind]()

  private def isOr(e: Axiom): Boolean = e match {
    case TypeAssertion(_, Or(_)) ⇒ true
    case _                       ⇒ false
  }

  private def getOrSet(s: Set[Axiom]): Set[TypeAssertion] = {
    val orSet: Set[Axiom] = s.filter(isOr);
    // TODO find other solution than type-casting
    return orSet.asInstanceOf[Set[TypeAssertion]]
  }

  def isSatisfiable(axiom: Axiom, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    return isSatisfiable(internalize(axiom, onto))
  }

  def isSatisfiable(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    val instance = nextInd()
    instanceSet += instance
    newSet += (TypeAssertion(instance, NNF.nnf(expr)) -> false)
    return TableauProof()
  }

  private def TableauProof(): (Boolean, Set[Set[Axiom]]) = {
    var orSet = getOrSet(newSet.filter(e ⇒ e._2 == false).keySet)
    var untestedSet = newSet.filter(e ⇒ e._2 == false)
    do {
      for (e ← untestedSet) {
        e._1 match {
          case RoleAssertion(r, a, b)  ⇒ Unit
          case TypeAssertion(a, Or(c)) ⇒ Unit
          case TypeAssertion(a, c)     ⇒ Tableau(a, c)
        }
        newSet = newSet.updated(e._1, true)
      }
      untestedSet = newSet.filter(e ⇒ e._2 == false).filterKeys(e ⇒ e.isInstanceOf[TypeAssertion] && !e.asInstanceOf[TypeAssertion].expr.isInstanceOf[Or])
      orSet ++= getOrSet(newSet.filter(e ⇒ e._2 == false).keySet)

    } while (untestedSet.size != 0)
    //proof or Expr
    if (!clash) {
      if (orSet.size != 0) TableauOr(orSet, newSet.keySet)
      else model += newSet.keySet
    }
    if (clash) println("clash")
    else println("model: " + model)

    return (clash, model)
  }

  private def TableauOr(orSet: Set[TypeAssertion], s: Set[Axiom]): Unit = {
    var oldmap: Map[Axiom, Boolean] = Map()
    var andSet: Set[Axiom] = Set[Axiom]()
    for (TypeAssertion(a, Or(cs)) ← orSet) {
      newSet = newSet.updated(TypeAssertion(a, Or(cs)), true)
      oldmap = newSet
      var i = 0
      for (f ← cs) {
        andSet = Set(TypeAssertion(a, f))
        clash = false
        do {
          for (a TypeAssertion c ← andSet) {
            if (!((c.isInstanceOf[Concept] || c.isInstanceOf[Not]) && newSet.keySet.contains(TypeAssertion(a, nnf(Not(c)))))) {
              Tableau(a, c)
              newSet = newSet.updated(TypeAssertion(a, c), true)
            } else clash = true
          }
          andSet = newSet.filter(e ⇒ e._2 == false).filterKeys(e ⇒ e.isInstanceOf[TypeAssertion] && !e.asInstanceOf[TypeAssertion].expr.isInstanceOf[Or]).keySet
        } while (andSet.size != 0 && !clash)
        if (!(newSet.filter(e ⇒ e._2 == false).keySet).filter(isOr).isEmpty) {
          TableauOr(getOrSet(newSet.filter(e ⇒ e._2 == false).keySet), newSet.keySet)
        } else if (!clash) model += newSet.keySet
        if (clash) i += 1
        newSet = oldmap
      }
      if (i == cs.size) clash = true
      else clash = false
    }
  }

  private def Tableau(i: Ind, f: Expr): Unit = f match {
    case And(expr)    ⇒ analyzeAnd(i, expr)
    case Exists(r, f) ⇒ analyzeExists(i, r, f)
    case ForAll(r, f) ⇒ analyzeForAll(i, r, f)
    case _            ⇒ newSet += (TypeAssertion(i, f) -> false)
  }

  private def analyzeForAll(x: Ind, r: Role, f: Expr): Unit = {
    var s = newSet.keySet
    for (e ← instanceSet) {
      if ((s contains RoleAssertion(r, x, e)) && !(s contains TypeAssertion(e, f))) {
        if ((f.isInstanceOf[Concept] || f.isInstanceOf[Not])
          && s.contains(TypeAssertion(e, nnf(Not(f))))) {
          clash = true
          return Unit
        } else {
          newSet += (TypeAssertion(e, f) -> false)
        }
      }
    }
  }

  private def analyzeExists(x: Ind, r: Role, f: Expr): Unit = {
    val y = nextInd()
    var s = newSet.keySet

    instanceSet += y
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
      if ((f.isInstanceOf[Concept] || f.isInstanceOf[Not]) && s.contains((TypeAssertion(y, nnf(Not(f)))))) {
        clash = true
        return Unit
      } else {
        if (!isBlocked(x, y, f)) {
          newSet += (RoleAssertion(r, x, y) -> false)
        } else { // y is blocked by x
          model += newSet.keySet
        }
      }
    }
  }

  private def isBlocked(x: Ind, y: Ind, f: Expr): (Boolean) = {
    var blocked = false
    var subset = Set[Expr](f)
    var xset = Set[Expr]()
    for (e ← newSet) {
      e._1 match {
        case RoleAssertion(r, a, b) ⇒ Unit
        case TypeAssertion(a, c) ⇒
          if (a.equals(x)) {
            xset += c
            c match {
              case Exists(role, form) ⇒ subset += form
              case ForAll(role, form) ⇒ subset += form
              case _                  ⇒ Unit
            }
          }
          newSet = newSet.updated(e._1, true)
      }
    }

    if (!subset.subsetOf(xset)) { // y is not blocked by x
      for (e ← subset) {
        if ((e.isInstanceOf[Concept] || e.isInstanceOf[Not]) && (newSet.keySet).contains((TypeAssertion(y, nnf(Not(e)))))) clash = true
        else {
          newSet += (TypeAssertion(y, e) -> false)
        }
      }
    } else
      blocked = true

    return (blocked)
  }

  private def analyzeAnd(instance: Ind, list: List[Expr]): Unit = {
    for (element ← list) {
      var subset = Set[Axiom]()
      if (element.isInstanceOf[And]) Tableau(instance, element)
      else {
        if ((element match {
          case Concept(_) ⇒ true
          case Not(_)     ⇒ true
          case _          ⇒ false
        }) && (newSet contains TypeAssertion(instance, nnf(Not(element))))) {
          clash = true
          return Unit
        } else {
          newSet += (TypeAssertion(instance, element) -> false)
        }
      }
    }
  }

}