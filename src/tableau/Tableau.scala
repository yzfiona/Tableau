package tableau;

import NNF.nnf


class TableauRules {

  private var counter: Int = 0;
  private def nextInd(): Ind = { counter += 1; return Ind("x" + counter) }

  private var instanceSet: Set[Ind] = Set[Ind]()

  private var clash: Boolean = false
  private var model = Set[Set[Axiom]]()

  def getOrSet(s: Set[Axiom]): Set[TypeAssertion] = {
    val orSet: Set[Axiom] = s.filter(_ match {
      case TypeAssertion(_, Or(_)) ⇒ true
      case _                       ⇒ false
    }
    );
    // TODO find other solution than type-casting
    return orSet.asInstanceOf[Set[TypeAssertion]]
  }

  def TableauProof(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    val instance = nextInd()
    instanceSet += instance
    var startingSet: Set[Axiom] = Set(TypeAssertion(instance, nnf(expr)))
    TableauProof(startingSet)
  }

  def TableauProof(s: Set[Axiom]): (Boolean, Set[Set[Axiom]]) = {
    var newSet = s
    var andSet = Set[Axiom]()
    var orSet = Set[TypeAssertion]()

    andSet = newSet
    orSet = getOrSet(newSet)
    do {
      var tempSet = newSet
      for (e ← andSet) {
        e match {
          case RoleAssertion(r, a, b)  ⇒ Unit
          case TypeAssertion(a, Or(c)) ⇒ Unit
          case TypeAssertion(a, c)     ⇒ newSet ++= Tableau(newSet, a, c)
        }
      }
      andSet = newSet -- tempSet
      orSet ++= getOrSet(newSet)

    } while (andSet.size != 0)
    //proof or Expr
    if (!clash) {
      if (orSet.size != 0) TableauOr(orSet, newSet)
      else model += newSet
    }
    if (clash) println("clash")
    else println("model: " + model)

    return (clash, model)
  }

  def TableauOr(orSet: Set[TypeAssertion], s: Set[Axiom]): Unit = {
    var newSet: Set[Axiom] = s
    var andSet: Set[Axiom] = Set[Axiom]()
    for (TypeAssertion(a, Or(cs)) ← orSet) {
      var AndSet_Set = analyzeOr(newSet, a, cs)
      var i = 0
      for (set ← AndSet_Set) {
        newSet = set
        andSet = set
        clash = false
        do {
          var tempset = newSet
          for (a TypeAssertion c ← andSet) {
            newSet ++= Tableau(newSet, a, c)
          }
          andSet = newSet -- tempset
        } while (andSet.size != 0)
        if (!getOrSet(newSet -- set).isEmpty) {
          TableauOr(getOrSet(newSet -- set), newSet)
        } else if (!clash) model += newSet
        if (clash) i += 1
      }
      if (i == AndSet_Set.size) clash = true
      else clash = false
    }
  }

  def Tableau(s: Set[Axiom], i: Ind, f: Expr): Set[Axiom] = f match {
    case And(expr)    ⇒ analyzeAnd(s, i, expr)
    case Exists(r, f) ⇒ analyzeExists(s, i, r, f)
    case ForAll(r, f) ⇒ analyzeForAll(s, i, r, f)
    case _            ⇒ Set(TypeAssertion(i, f))
  }

  def analyzeOr(s: Set[Axiom], instance: Ind, list: List[Expr]): Set[Set[Axiom]] = {
    var setlist = Set[Set[Axiom]]()
    for (element ← list) {
      if (!((element.isInstanceOf[Concept] || element.isInstanceOf[Not]) && s.contains(TypeAssertion(instance, nnf(Not(element)))))) {
        setlist += (s + TypeAssertion(instance, element))
      }
    }
    return setlist
  }

  def analyzeForAll(s: Set[Axiom], x: Ind, r: Role, f: Expr): Set[Axiom] = {
    var newSet = s
    for (e ← instanceSet) {
      if ((s contains RoleAssertion(r, x, e)) && !(s contains TypeAssertion(e, f))) {
        if ((f.isInstanceOf[Concept] || f.isInstanceOf[Not])
          && s.contains(TypeAssertion(e, nnf(Not(f))))) {
          clash = true
          return s
        } else newSet += TypeAssertion(e, f)
      }
    }
    return newSet
  }

  def analyzeExists(s: Set[Axiom], x: Ind, r: Role, f: Expr): Set[Axiom] = {
    var newSet = s
    val y = nextInd()

    instanceSet += y
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
      if ((f.isInstanceOf[Concept] || f.isInstanceOf[Not]) && s.contains((TypeAssertion(y, nnf(Not(f)))))) {
        clash = true
        return s
      } else {
        var blocked = isBlocked(s, x, y, f)
        if (blocked._2 == false) {
          newSet += RoleAssertion(r, x, y)
          //newSet += TypeAssertion(y, f)
          newSet ++= blocked._1
        } else { // y is blocked by x
          model += newSet
        }
      }
    }
    return newSet
  }

  def isBlocked(s: Set[Axiom], x: Ind, y: Ind, f: Expr): (Set[Axiom], Boolean) = {
    var blocked = false
    var newSet = Set[Axiom]()
    var subset = Set[Expr](f)
    var xset = Set[Expr]()
    //testedSet = Set[Axiom]()
    for (e ← s) {
      e match {
        case RoleAssertion(r, a, b) ⇒ Unit
        case TypeAssertion(a, c) ⇒
          if (a.equals(x)) {
            xset += c
            c match {
              case Exists(role, form) ⇒ subset += form
              case ForAll(role, form) ⇒ subset += form
              case _                  ⇒ Unit
            }
            //  testedSet += e
          }
      }
    }

    if (!subset.subsetOf(xset)) { // y is not blocked by x
      for (e ← subset) {
        if ((e.isInstanceOf[Concept] || e.isInstanceOf[Not]) && (s ++ newSet).contains((TypeAssertion(y, nnf(Not(e)))))) clash = true
        else newSet += TypeAssertion(y, e)
      }
    } else
      blocked = true

    return (newSet, blocked)
  }

  def analyzeAnd(s: Set[Axiom], instance: Ind, list: List[Expr]): Set[Axiom] = {
    var newSet = s
    for (element ← list) {
      var subset = Set[Axiom]()
      /* TODO the case And(And(...)) should not occur
      if (element.isInstanceOf[And]) subset ++= Tableau(newSet, instance, element) 
      else*/ subset += TypeAssertion(instance, element)
      //if (clash) return s
      for (TypeAssertion(a, c) ← subset) {
        if ((c match {
          case Concept(_) ⇒ true
          case Not(_)     ⇒ true
          case _          ⇒ false
        }) && (newSet contains TypeAssertion(instance, nnf(Not(c))))) {
          clash = true
          return s
        } else newSet += TypeAssertion(a, c)
      }
    }
    return newSet

  }

}