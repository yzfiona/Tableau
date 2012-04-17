package tableau

import NNF.nnf
import tableau.Internalization.internalize
import model.OntologySpec._
import datastructure.NTree
import datastructure.TreeNode
//import scala.util.control.Breaks._

class OptimizedTableau {

  private var counter: Int = 0
  private def nextInd(): Ind = { counter += 1; return Ind("x" + counter) }
  private var instanceSet: Set[Ind] = Set[Ind]()

  private var clash: Boolean = false
  private var model = Set[Set[Axiom]]()
  private var newSet: Map[Axiom, Boolean] = Map()
  
  private var onto : Expr = null
  
  private var Tree = new NTree()
  private var currentNode = new TreeNode()

  def isSatisfiable(axiom: Axiom, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    this.onto = And(removeRedudantAnd(NNF.nnf(internalize(onto))))
    return isSatisfiable(axiom.toConcept, onto)
  }
  
  def isSatisfiable(expr: Expr, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    this.onto = And(removeRedudantAnd(NNF.nnf(internalize(onto))))
    return isSatisfiable(internalize(onto) and expr)//(internalize(onto)) and Not(expr))
  }

  def isSatisfiable(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    val instance = nextInd()
    instanceSet += instance
    val axiom = TypeAssertion(instance, And(removeRedudantAnd(NNF.nnf(expr))))
    newSet += (axiom -> false)
    Tree.insert(axiom)
    currentNode = Tree.getRoot()
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
          case TypeAssertion(a, maxCardinality(n, r, f)) => Unit
          case TypeAssertion(a, c)     ⇒ Tableau(a, c)
        }
        newSet = newSet.updated(e._1, true)
      }
      //build the test set which doesn't contain or and maxCardinality
      untestedSet = newSet.filter(e ⇒ e._2 == false && 
    		  					 (e._1 match {
    		  						case TypeAssertion(_, Or(_)) => false
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => false
    		  						case RoleAssertion(_, _, _) => false
    		  						case _ => true
    		  					 }))
         
      orSet ++= getOrSet(newSet.filter(e ⇒ e._2 == false).keySet)
    } while (untestedSet.size != 0)
    //proof or Expr
    if (!clash) {
      if (orSet.size != 0) analyzeOr(orSet.first, newSet.keySet)
      else {
        untestedSet = newSet.filter(e => e._2 == false && 
        								(e._1 match {
          									  case TypeAssertion(_, maxCardinality(_, _, _)) => true
          						    		  case _ => false
        								}))
        if (untestedSet.size != 0) {
          for (TypeAssertion(x, expr: maxCardinality) <- untestedSet.keySet) {
              //a rule for expressions such as ≤nR.A ⊓ ≤nR.¬A
        	  if (newSet.keySet.contains((TypeAssertion(x, maxCardinality(expr.n, expr.r, Not(expr.f)))))) {
        	    clash = true 	    
        	  }
        	  else if (!clash) analyzemaxCardinality(x, expr.n, expr.r, expr.f) 
          }
        } else model += newSet.keySet       
      }      
    }
    if (clash) println("clash")
    else println("model: " + model)
    Tree.print();

    return (clash, model)
  }
  
    private def getOrSet(s: Set[Axiom]): Set[TypeAssertion] = {
    val orSet: Set[Axiom] = s.filter(e => e match {
       									case TypeAssertion(_, Or(_)) ⇒ true
       									case _                       ⇒ false 
    								});
    // TODO find other solution than type-casting
    return orSet.asInstanceOf[Set[TypeAssertion]]
  }
     
  private def Tableau(i: Ind, f: Expr): Unit = f match {
    case And(expr)    ⇒ analyzeAnd(i, expr)
    case Exists(r, f) ⇒ analyzeExists(i, r, f)
    case ForAll(r, f) ⇒ analyzeForAll(i, r, f)
    case minCardinality(n, r, f) => analyzeminCardinality(i, n, r)
    case Concept(c) => newSet = newSet.updated(TypeAssertion(i, f), true)
    case Not(Concept(c)) => newSet = newSet.updated(TypeAssertion(i, f), true)
    case _            ⇒  Unit//println("Error: No matched pattern found")
  }

  private def analyzeOr(or: TypeAssertion, s: Set[Axiom]): Unit = {
    var oldmap: Map[Axiom, Boolean] = Map()
    var oldinstanceSet: Set[Ind] = Set()
    var andSet: Set[Axiom] = Set[Axiom]()
    var BranchNode = currentNode
    var orSet : Set[TypeAssertion] = Set()
   // for (TypeAssertion(a, Or(cs)) ← orSet) {
    or match {
      case TypeAssertion(a, Or(cs)) =>
      newSet = newSet.updated(or, true)//TypeAssertion(a, Or(cs)), true)
      oldmap = newSet
      oldinstanceSet = instanceSet
      var i = 0
      if (!clash) {
        for (f ← cs) {
        andSet = Set(TypeAssertion(a, f)) 
        currentNode = Tree.insert(currentNode, TypeAssertion(a, f))
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
        		  					case TypeAssertion(_, maxCardinality(_, _, _)) => false
        		  					case RoleAssertion(_, _, _) => false
        		  					case _ => true
        		  				})).keySet
        } while (andSet.size != 0 && !clash)
          orSet = getOrSet(newSet.filter(e ⇒ e._2 == false).keySet)
        if (!orSet.isEmpty && !clash) {
          analyzeOr(orSet.first, newSet.keySet)
        } else if (!clash) {
          //to check maxCardinality
          var maxSet = newSet.filter(e => e._1 match {
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => true
    		  						case _ => false
    		  					}).keySet
          if (maxSet.size == 0) model += newSet.keySet
          else {
        	  	var breakflag = false
        	  	var iterator = maxSet.iterator
            	while(!breakflag && iterator.hasNext) {//for (TypeAssertion(ind, maxCardinality(n, r)) <- maxSet) {
            	    val e = iterator.next().asInstanceOf[TypeAssertion]
            	    //FIXME type-casting
            	    val f = e.expr.asInstanceOf[maxCardinality]
            		analyzemaxCardinality(e.a, f.n, f.r, f.f)
            		if (clash) breakflag = true//FIXME break
            	}
          }          
        }
        if (clash) i += 1
        newSet = oldmap
        currentNode = BranchNode
        instanceSet = oldinstanceSet
      }
      if (i == cs.size) clash = true
      else clash = false
      }
    }
  }
  
  private def analyzeminCardinality(x: Ind, n: Integer, r: Role): Unit = {
    if (newSet.filterKeys(e => e match {
      							case RoleAssertion(r, x, _) => true
      							case _ => false
    }).size < n) {
        for (i <- 1 to n){
        	val y = nextInd()
        	var s = newSet.keySet
        	instanceSet += y
        	newSet += (RoleAssertion(r, x, y) -> false)	   	
        	currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
        }
    }
    //TODO how about Exists?
    for (TypeAssertion(x, c) <- newSet.filterKeys(e => e match {
      															case TypeAssertion(x, ForAll(r, _)) => true
      															case _ => false}).keySet) {
      Tableau(x, c)
    }
  }
  
  private def analyzemaxCardinality(x: Ind, n: Integer, r: Role, f: Expr): Unit = {

    
    //FIXME type-casting
    var orSet : Set[RoleAssertion] = Set[RoleAssertion]()
    var oldmap = newSet
    var count: Integer = 0
    var roleSet : List[RoleAssertion] = List[RoleAssertion]()
    if (f.equals(Top)) roleSet = newSet.filterKeys(e => e match {
      									case RoleAssertion(r, x, _) => true
      									case _ => false
    								}).keySet.toList.asInstanceOf[List[RoleAssertion]]
    else roleSet = newSet.filterKeys(e => e match {
      									case RoleAssertion(r, x, y) => newSet.keySet.contains(TypeAssertion(y, f))
      									case _ => false
    								}).keySet.toList.asInstanceOf[List[RoleAssertion]]
    if (roleSet.size > n){
      for ( i <- 1 until roleSet.size) {
      //replace and take the or into account
      var replacedInd = Set[Ind]()
      var replaceInd = roleSet.apply(i).b
      for (j <- 0 until i){
       replacedInd += roleSet.apply(j).b
      }
     for(instance <- replacedInd) {
        //update newSet by replacing all replacedInd with replaceInd
        var breakflag = false
        var iterator = oldmap.iterator
        while(!breakflag && iterator.hasNext) {//for ( e <- newSetbackup){
          var e = iterator.next()
          e._1 match {
            case TypeAssertion(ind, expr) =>
            if (ind.equals(instance)) {
                  var result = currentNode.find(TypeAssertion(instance, expr))
                  if (result != null) currentNode = result
            	  if ((expr match {
            	  		case Concept(_) ⇒ true
            	  		case Not(_)     ⇒ true
            	  		case _          ⇒ false
            	  }) && (newSet.keySet contains TypeAssertion(replaceInd, nnf(Not(expr))))) {
            	    clash = true;            	    
            	    if (result != null)  currentNode.updateValue(TypeAssertion(replaceInd, expr))
            	    //FIXME should break out the for loop
            	    //break;
            	    breakflag = true
            	  }
            	  else {
            	    newSet = newSet.-(e._1).+(TypeAssertion(replaceInd, expr) -> false)
            	    if (result != null)   currentNode.updateValue(TypeAssertion(replaceInd, expr))
            	  }
            }
            case RoleAssertion(role, ind1, ind2) =>
              var result = currentNode.find(RoleAssertion(role, ind1, ind2))
              if (result != null) currentNode = result
              if (ind1.equals(instance) && ind2.equals(instance)) {
                newSet = newSet.-(e._1).+(RoleAssertion(role, replaceInd, replaceInd) -> false)
                 if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, replaceInd))               
              }
              else if (ind1.equals(instance)) {
                newSet = newSet.-(e._1).+(RoleAssertion(role, replaceInd, ind2) -> false)
                 if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, ind2))    
              }
              else if (ind2.equals(instance)) {
                newSet = newSet.-(e._1).+(RoleAssertion(role, ind1, replaceInd) -> false)
                 if (result != null)  currentNode.updateValue(RoleAssertion(role, ind1, replaceInd))   
              }
            case _ => Unit
          }
        }
        //check all the possibilities
        if (!clash) model += newSet.keySet
        else {count += 1; clash = false}
        newSet = oldmap
      }
    }
    if (count == roleSet.size -1 ) clash = true
    else clash = false
    }
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
          currentNode = Tree.insert(currentNode, TypeAssertion(x, f))
          //Tree.insert(currentNode, TypeAssertion(e, Bottom))
          return Unit
        } else {
          newSet += (TypeAssertion(e, f) -> false)
          currentNode = Tree.insert(currentNode, TypeAssertion(e, f))
        }
      }
    }
  }

  private def analyzeExists(x: Ind, r: Role, f: Expr): Unit = {
    var s = newSet.keySet   
    val y = nextInd()
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
        if (isBlocked(x, y, r, f)) { // y is blocked by x
          model += newSet.keySet
        }
    }

  }

 
  private def isBlocked(x: Ind, y: Ind, r: Role, f: Expr): (Boolean) = {
    var blocked = false
    var subset = Set[Expr](f)
    var allset = Set[Set[Expr]]()
    val iterator1 = instanceSet.iterator
    var instance = iterator1.next()
    //to check if y is blocked by any of its ancestors
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
    // to calculate the expressions under the instance node y
    for (TypeAssertion(a, c) ← newSet.filterKeys(e => e match {
          							case TypeAssertion(x, ForAll(r,_)) => true
          							case TypeAssertion(x, Exists(r, f)) => true
          							case _ => false
      								}).keySet) {
       c match {
              //case Exists(role, form) ⇒ subset += form ; newSet = newSet.updated(TypeAssertion(a, c), true)
              case ForAll(r, form) ⇒ subset += form ; newSet = newSet.updated(TypeAssertion(a, c), true)
              case _                  ⇒ Unit
      }
    }
    subset += f
    newSet = newSet.updated(TypeAssertion(x, Exists(r, f)), true)
    //to check blocking
    val iterator2 = allset.iterator
    var breakflag = false
    while (!breakflag && iterator2.hasNext) {
      val xset = iterator2.next()
      if (subset.subsetOf(xset)) { // y is blocked by x
    	  blocked = true    	  
    	  breakflag = true
      } 
    }
    //if not blocked, to add all expressions with instance y into newSet
    if (!blocked) {
          currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
          instanceSet += y
          newSet += (RoleAssertion(r, x, y) -> false)         
          if (this.onto != null) { 
        	  currentNode = Tree.insert(currentNode, TypeAssertion(y, this.onto))
        	  newSet += (TypeAssertion(y, this.onto) -> false)
          }
          for (e ← subset) {
    		  if ((e.isInstanceOf[Concept] || e.isInstanceOf[Not]) && (newSet.keySet).contains((TypeAssertion(y, nnf(Not(e)))))){
    		    clash = true
    		    currentNode = Tree.insert(currentNode, TypeAssertion(y, e))
    		    //Tree.insert(currentNode, TypeAssertion(y,Bottom))
    		  } 
    		  else {
    			newSet += (TypeAssertion(y, e) -> false)
    			currentNode = Tree.insert(currentNode, TypeAssertion(y,e))
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
          currentNode = Tree.insert(currentNode, TypeAssertion(x, element))
          //Tree.insert(currentNode,TypeAssertion(x, Bottom))
          return Unit
        } else {
          newSet += (TypeAssertion(x, element) -> false)
          currentNode = Tree.insert(currentNode,TypeAssertion(x, element))
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
        	   	case Or(_) => list = Or(removeRedudantOr(element.asInstanceOf[Or])) :: list
        	   	case _ => list = element::list
        	   }
           }
      case _ => Unit
    }
    return list.reverse
  }
  
    private def removeRedudantOr(expr: Expr): List[Expr] = {
    var list = List[Expr]()
    expr match {
      case Or(f) =>
           for (element <- f) {
        	   element match {
        	   	case Or(_) => list = removeRedudantOr(element.asInstanceOf[Or]) ::: list
        	   	case _ => list = element::list
        	   }
           }
      case _ => Unit
    }
    return list.reverse
  }

}