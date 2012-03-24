package tableau;

import NNF.nnf
import tableau.Internalization.internalize
import model.OntologySpec._
//import scala.util.control.Breaks._

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
    return isSatisfiable(axiom.toConcept, onto)
  }
  
  def isSatisfiable(expr: Expr, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    return isSatisfiable(Not(Not(internalize(onto)) or expr))
  }

  def isSatisfiable(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    val instance = nextInd()
    instanceSet += instance
    newSet += (TypeAssertion(instance, And(removeRedudantAnd(NNF.nnf(expr)))) -> false)
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
          case TypeAssertion(a, maxCardinality(n, r)) => Unit
          case TypeAssertion(a, c)     ⇒ Tableau(a, c)
        }
        newSet = newSet.updated(e._1, true)
      }
      //build the test set which doesn't contain or and maxCardinality
      untestedSet = newSet.filter(e ⇒ e._2 == false && 
    		  					 (e._1 match {
    		  						case TypeAssertion(_, Or(_)) => false
    		  						case TypeAssertion(_, maxCardinality(_, _)) => false
    		  						case RoleAssertion(_, _, _) => false
    		  						case _ => true
    		  					 }))
         
      orSet ++= getOrSet(newSet.filter(e ⇒ e._2 == false).keySet)
    } while (untestedSet.size != 0)
    //proof or Expr
    if (!clash) {
      if (orSet.size != 0) analyzeOr(orSet, newSet.keySet)
      else model += newSet.keySet
    }
    if (clash) println("clash")
    else println("model: " + model)

    return (clash, model)
  }

  private def analyzeOr(orSet: Set[TypeAssertion], s: Set[Axiom]): Unit = {
    var oldmap: Map[Axiom, Boolean] = Map()
    var andSet: Set[Axiom] = Set[Axiom]()
    for (TypeAssertion(a, Or(cs)) ← orSet) {
      newSet = newSet.updated(TypeAssertion(a, Or(cs)), true)
      oldmap = newSet
      var i = 0
      if (!clash) {
        for (f ← cs) {
        andSet = Set(TypeAssertion(a, f))        
        clash = false
        do {
          for (a TypeAssertion c ← andSet) {
            if ((c match {
            	case Concept(_) ⇒ true
            	case Not(_)     ⇒ true
            	case _          ⇒ false
            }) && (newSet.keySet contains TypeAssertion(a, nnf(Not(c))))) {
            	clash = true
            } else {
            	Tableau(a, c)
            	newSet = newSet.updated(TypeAssertion(a, c), true)
            }
          }
          andSet = newSet.filter(e ⇒ e._2 == false && 
        		  				(e._1 match {
        		  					case TypeAssertion(_, Or(_)) => false
        		  					case TypeAssertion(_, maxCardinality(_, _)) => false
        		  					case RoleAssertion(_, _, _) => false
        		  					case _ => true
        		  				})).keySet
        } while (andSet.size != 0 && !clash)
        if (!(newSet.filter(e ⇒ e._2 == false).keySet).filter(isOr).isEmpty && !clash) {
          analyzeOr(getOrSet(newSet.filter(e ⇒ e._2 == false).keySet), newSet.keySet)
        } else if (!clash) {
          //TODO to check maxCardinality
          var maxSet = newSet.filter(e => e._1 match {
    		  						case TypeAssertion(_, maxCardinality(_, _)) => true
    		  						case _ => false
    		  					}).keySet
          if (maxSet.size == 0) model += newSet.keySet
          else {
        	  	var breakflag = false
        	  	var iterator = maxSet.iterator
            	while(!breakflag && iterator.hasNext) {//for (TypeAssertion(ind, maxCardinality(n, r)) <- maxSet) {
            	    val e = iterator.next().asInstanceOf[TypeAssertion]
            	    val f = e.expr.asInstanceOf[maxCardinality]
            		analyzemaxCardinality(e.a, f.n, f.r)
            		if (clash) breakflag = true//FIXME break
            	}
          }          
        }
        if (clash) i += 1
        newSet = oldmap
      }
      if (i == cs.size) clash = true
      else clash = false
      }
    }
  }

  private def Tableau(i: Ind, f: Expr): Unit = f match {
    case And(expr)    ⇒ analyzeAnd(i, expr)
    case Exists(r, f) ⇒ analyzeExists(i, r, f)
    case ForAll(r, f) ⇒ analyzeForAll(i, r, f)
    case minCardinality(n, r) => analyzeminCardinality(i, n, r)
    case _            ⇒ newSet += (TypeAssertion(i, f) -> false)
  }
  
  private def analyzeminCardinality(x: Ind, n: Integer, r: Role): Unit = {
    if (/*!isBlocked(x, null, null) &&*/ newSet.filterKeys(e => e match {
      							case RoleAssertion(r, x, _) => true
      							case _ => false
    }).size < n) {
        for (i <- 1 to n){
        	val y = nextInd()
        	var s = newSet.keySet
        	instanceSet += y
        	newSet += (RoleAssertion(r, x, y) -> false)	   	
        }
    }
    //TODO how about Exists?
    for (TypeAssertion(x, c) <- newSet.filterKeys(e => e match {
      															case TypeAssertion(x, ForAll(r, _)) => true
      															case _ => false}).keySet) {
      Tableau(x, c)
    }
  }
  
  private def analyzemaxCardinality(x: Ind, n: Integer, r: Role): Unit = {
    var roleSet: List[RoleAssertion] = newSet.filterKeys(e => e.isInstanceOf[RoleAssertion] &&  e.asInstanceOf[RoleAssertion].r.equals(r) && e.asInstanceOf[RoleAssertion].a.equals(x)).keySet.toList.asInstanceOf[List[RoleAssertion]]
    var orSet : Set[RoleAssertion] = Set[RoleAssertion]()
    var newSetbackup = newSet
    var count: Integer = 0
    for ( i <- 1 until roleSet.size) {
      //replace and take the or into account
      var toreplaceInd = Set[Ind]()
      var replaceInd = roleSet.apply(i).b
      for (j <- 0 until i){
        toreplaceInd += roleSet.apply(j).b
      }
     for(instance <- toreplaceInd) {
        //update newSet by replacing all tobereplacedInd with replaceInd
        var breakflag = false
        var iterator = newSetbackup.iterator
        while(!breakflag && iterator.hasNext) {//for ( e <- newSetbackup){
          var e = iterator.next()
          e._1 match {
            case TypeAssertion(ind, expr) =>
              if (ind.equals(instance)) {
            	  if ((expr match {
            	  		case Concept(_) ⇒ true
            	  		case Not(_)     ⇒ true
            	  		case _          ⇒ false
            	  }) && (newSet.keySet contains TypeAssertion(replaceInd, nnf(Not(expr))))) {
            	    clash = true;
            	    //FIXME should break out the for loop
            	    //break;
            	    breakflag = true
            	  }
            	  else newSet = newSet.-(e._1).+(TypeAssertion(replaceInd, expr) -> false)
              }
            case RoleAssertion(role, ind1, ind2) =>
              if (ind1.equals(instance) && ind2.equals(instance)) newSet = newSet.-(e._1).+(RoleAssertion(role, replaceInd, replaceInd) -> false)
              else if (ind1.equals(instance)) newSet = newSet.-(e._1).+(RoleAssertion(role, replaceInd, ind2) -> false)
              else if (ind2.equals(instance)) newSet = newSet.-(e._1).+(RoleAssertion(role, ind1, replaceInd) -> false)
            case _ => Unit
          }
        }
        //check all the possibilities
        if (!clash) model += newSet.keySet
        else {count += 1; clash = false}
        newSet = newSetbackup
      }
    }
    if (count == roleSet.size -1 ) clash = true
    else clash = false
  }

  private def analyzeForAll(x: Ind, r: Role, f: Expr): Unit = {
    var s = newSet.keySet
    for (e ← instanceSet) {
      if ((s contains RoleAssertion(r, x, e)) && !(s contains TypeAssertion(e, f))) {
        if ((f match {
          case Concept(_) ⇒ true
          case Not(_)     ⇒ true
          case _          ⇒ false
        }) && (s contains TypeAssertion(e, nnf(Not(f))))) {
          clash = true
          return Unit
        } else {
          newSet += (TypeAssertion(e, f) -> false)
        }
      }
    }
  }

  private def analyzeExists(x: Ind, r: Role, f: Expr): Unit = {
   // var ySet = Set[Ind]()
    var s = newSet.keySet
    /*for (RoleAssertion(r, x, y) <- newSet.filterKeys(e => e match {
      								case RoleAssertion(r, x, _) => true
      								case _ => false}).keySet){
      if (!(s contains TypeAssertion(y, f))) ySet += y
    }        
    if (ySet.size == 0) {
      val instance = nextInd()
      ySet += instance
      instanceSet += instance
    }
    for (y <- ySet) {
       if (!isBlocked(x, y, f)) {
         instanceSet += y
         newSet += (RoleAssertion(r, x, y) -> false)
       } else { // y is blocked by x
         model += newSet.keySet
       } 
    }*/
    
    val y = nextInd()
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
        if (!isBlocked(x, y, f)) {
          instanceSet += y
          newSet += (RoleAssertion(r, x, y) -> false)
        } else { // y is blocked by x
          model += newSet.keySet
        }
    }

  }

 
  private def isBlocked(x: Ind, y: Ind, f: Expr): (Boolean) = {
    var blocked = false
    var subset = Set[Expr](f)
    var allset = Set[Set[Expr]]()
    val iterator1 = instanceSet.iterator
    var instance = iterator1.next()
    while (!instance.equals(x)){
      allset += (for (TypeAssertion(i, f) <- newSet.filterKeys(e => e match {
          													case TypeAssertion(instance, _) => true
          													case _ => false
      								}).keySet) yield {f})
      instance = iterator1.next()
    }
    
    allset += (for (TypeAssertion(i, f) <- newSet.filterKeys(e => e match {
          													case TypeAssertion(x, _) => true
          													case _ => false
      								}).keySet) yield {f})

    for (e ← newSet) {
      e._1 match {
        case TypeAssertion(a, c) ⇒
          if (a.equals(x)) {
            c match {
              case Exists(role, form) ⇒ subset += form ; newSet = newSet.updated(e._1, true)
              case ForAll(role, form) ⇒ subset += form ; newSet = newSet.updated(e._1, true)
              case _                  ⇒ Unit
            }
          }
        case _ ⇒ Unit
      }
    }
    val iterator2 = allset.iterator
    var breakflag = false
    while (!breakflag && iterator2.hasNext) {
      val xset = iterator2.next()
      if (subset.subsetOf(xset)) { // y is blocked by x
    	  blocked = true    	  
    	  breakflag = true
      } 
    }
    if (!blocked) {
          for (e ← subset) {
    		  if ((e.isInstanceOf[Concept] || e.isInstanceOf[Not]) && (newSet.keySet).contains((TypeAssertion(y, nnf(Not(e)))))) clash = true
    		  else {
    			newSet += (TypeAssertion(y, e) -> false)
    		  }
    	  }
    }
    return (blocked)
  }

  private def analyzeAnd(x: Ind, list: List[Expr]): Unit = {
    for (element ← list) {
      var subset = Set[Axiom]()
      if (element.isInstanceOf[And]) Tableau(x, element)
      else {
        if ((element match {
          case Concept(_) ⇒ true
          case Not(_)     ⇒ true
          case _          ⇒ false
        }) && (newSet contains TypeAssertion(x, nnf(Not(element))))) {
          clash = true
          return Unit
        } else {
          newSet += (TypeAssertion(x, element) -> false)
        }
      }
    }
  }
  
  private def removeRedudantAnd(expr: Expr): List[Expr] = {
    var list = List[Expr]()
    expr match {
      case And(f) =>
           for (element <- f) {
        	   element match {
        	   	case And(_) => list = removeRedudantAnd(element.asInstanceOf[And]) ::: list
        	   	case _ => list = element::list
        	   }
           }
      case _ => Unit
    }
    return list.reverse
  }

}