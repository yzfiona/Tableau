package tableau

import NNF.nnf
import tableau.Internalization.internalize
import datastructure.NTree
import datastructure.TreeNode
import model.Ontology
import dk.brics.automaton.Automaton
//import scala.util.control.Breaks._

class OptimizedTableau {

  private var counter: Int = 0
  private def nextInd(): Ind = { counter += 1; return Ind("x" + counter) }
  private var instanceSet: Set[Ind] = Set[Ind]()
  private var notEqInstance : Set[Set[Ind]] = Set[Set[Ind]]()

  private var clash: Boolean = false
  private var model = Set[Set[Axiom]]()
  private var axiomMap: Map[Axiom, Boolean] = Map()
  
  private var tbox : Expr = null
  private var onto : Ontology = null
  
  private var Tree = new NTree()
  private var currentNode = new TreeNode()

  def isSatisfiable(axiom: TBoxAxiom, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    return isSatisfiable(axiom.toConcept, onto)
  }
  
  def isSatisfiable(axiom: ABoxAxiom, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    this.tbox = And(removeRedudantAnd(NNF.nnf(internalize(onto.TBox))))
    this.onto = onto.addAxiom(axiom)
    return isSatisfiable(internalize(onto.TBox))
  }
  
  def isSatisfiable(expr: Expr, onto : Ontology): (Boolean, Set[Set[Axiom]]) = {
    this.tbox = And(removeRedudantAnd(NNF.nnf(internalize(onto.TBox))))
    this.onto = onto
    return isSatisfiable(internalize(onto.TBox) and expr)//(internalize(onto)) and Not(expr))
  }

  def isSatisfiable(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    var toDo = false
    expr match {
      case And(c) => if (c.size != 0) toDo = true
      case _ => true
    }
    if (toDo) {
    	val instance = nextInd()
    	instanceSet += instance
    	val axiom = TypeAssertion(instance, And(removeRedudantAnd(NNF.nnf(expr))))
    	axiomMap += (axiom -> false)
    }
    if (this.onto != null) {
      for (axiom <- this.onto.ABox) {
        axiomMap += (axiom -> false)
        axiom match {
          case RegExprClass(_,_) => Unit
          case TypeAssertion(ind, expr) => instanceSet += ind
          case RoleAssertion(r, ind1, ind2) => instanceSet = instanceSet ++ Set(ind1,ind2)
          case NotEquivalentIndividual(ind1, ind2) => 
            	instanceSet = instanceSet ++ Set(ind1,ind2)
            	var set = notEqInstance.find( e => e.contains(ind1) && e.contains(ind2))
            	if (set.size == 0) notEqInstance += Set(ind1, ind2)
            	else notEqInstance = notEqInstance.-(set.first).+(set.first+(ind1)+(ind2))
        }
      }
    }
    return TableauProof()
  }

  private def TableauProof(): (Boolean, Set[Set[Axiom]]) = {
    var orSet = getOrSet(axiomMap.filter(e ⇒ e._2 == false).keySet)
    var untestedSet = axiomMap.filter(e ⇒ e._2 == false)
    Tree.insert(axiomMap.keySet.first)
    currentNode = Tree.getRoot()
    do {
      for (e ← untestedSet) {
        e._1 match {
          case RoleAssertion(r, a, b)  ⇒ Unit
          case TypeAssertion(a, Or(c)) ⇒ Unit
          case NotEquivalentIndividual(_,_) => Unit
          case RegExprClass(_,_) => Unit
          case TypeAssertion(a, maxCardinality(n, r, f)) => Unit
          case TypeAssertion(a, c)     ⇒ 
          	Tableau(a, c)
          	axiomMap = axiomMap.updated(e._1, true)
        }
      }
      //build the test set which doesn't contain or and maxCardinality
      untestedSet = axiomMap.filter(e ⇒ e._2 == false && 
    		  					 (e._1 match {
    		  						case TypeAssertion(_, Or(_)) => false
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => false
    		  						case RegExprClass(_,_) => false
    		  						case RoleAssertion(_, _, _) => false
    		  						case _ => true
    		  					 }))
         
      orSet ++= getOrSet(axiomMap.filter(e ⇒ e._2 == false).keySet)
    } while (untestedSet.size != 0)
    //proof or Expr
    if (!clash && !checkCardinality) {
      if (orSet.size != 0) analyzeOr(orSet.first, axiomMap.keySet)
      else {
        untestedSet = axiomMap.filter(e => e._2 == false && 
        								(e._1 match {
          									  case TypeAssertion(_, maxCardinality(_, _, _)) => true
          						    		  case _ => false
        								}))
        if (untestedSet.size != 0) {
          for (TypeAssertion(x, expr: maxCardinality) <- untestedSet.keySet) {
            /*  //a rule for expressions such as ≤nR.A ⊓ ≤nR.¬A
        	  if (axiomMap.keySet.contains((TypeAssertion(x, maxCardinality(expr.n, expr.r, Not(expr.f)))))) {
        	    clash = true 	    
        	  }
        	  else if (!clash) */analyzemaxCardinality(x, expr.n, expr.r, expr.f) 
          }
        }
        if(!clash) {
          untestedSet = axiomMap.filter(e =>e._1 match {
          									case RegExprClass(_, _) => true
          						    		case _ => false
        							   })
          if (untestedSet.size != 0) analyzeRegExpr(untestedSet.keySet)
        }     
        if (!clash) model += axiomMap.keySet
      }      
    }
    if (clash) println("clash")
    else println("model: " + model)
   // Tree.print();

    return (clash, model)
  }
     
  private def Tableau(i: Ind, f: Expr): Unit = f match {
    case And(expr)    ⇒ analyzeAnd(i, expr)
    case Exists(r, f) ⇒ analyzeExists(i, r, f)
    case ForAll(r, f) ⇒ analyzeForAll(i, r, f)
    case minCardinality(n, r, f) => analyzeminCardinality(i, n, r, f)
    case Concept(c) => axiomMap = axiomMap.updated(TypeAssertion(i, f), true)
    case Not(Concept(c)) => axiomMap = axiomMap.updated(TypeAssertion(i, f), true)
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
      axiomMap = axiomMap.updated(or, true)//TypeAssertion(a, Or(cs)), true)
      oldmap = axiomMap
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
            }) && (axiomMap.keySet contains TypeAssertion(a, nnf(Not(c))))) {
            	clash = true    	
            } else {
            	Tableau(a, c)
            	axiomMap = axiomMap.updated(TypeAssertion(a, c), true)
            }
          }
          andSet = axiomMap.filter(e ⇒ e._2 == false && 
        		  				(e._1 match {
        		  					case TypeAssertion(_, Or(_)) => false
        		  					case TypeAssertion(_, maxCardinality(_, _, _)) => false
        		  					case RoleAssertion(_, _, _) => false
        		  					case _ => true
        		  				})).keySet
        } while (andSet.size != 0 && !clash)
          orSet = getOrSet(axiomMap.filter(e ⇒ e._2 == false).keySet)
        if (!orSet.isEmpty && !clash) {
          analyzeOr(orSet.first, axiomMap.keySet)
        } else if (!clash) {
          //to check maxCardinality
          var maxSet = axiomMap.filter(e => e._1 match {
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => true
    		  						case _ => false
    		  					}).keySet
          if (maxSet.size == 0) model += axiomMap.keySet
          else if (!checkCardinality){
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
        if (!clash) {
          var untestedSet = axiomMap.filter(e =>e._1 match {
          									case RegExprClass(_, _) => true
          						    		case _ => false
        							   }).keySet
          if (untestedSet.size != 0) analyzeRegExpr(untestedSet)
        }
        if (clash) i += 1
        axiomMap = oldmap
        currentNode = BranchNode
        instanceSet = oldinstanceSet
      }
      if (i == cs.size) clash = true
      else clash = false
      }
    }
  }
  
  private def analyzeRegExpr(RegSet: Set[Axiom]) {
    var ConAstSet = axiomMap.filter(e =>e._1 match {
          									case TypeAssertion(_, Concept(_)) => true
          						    		case _ => false
        							   }).keySet
    var ConceptMap: Map[Ind, Set[Concept]] = Map()
    var RegMap: Map[Concept, String] = (for (RegExprClass(c, regExpr) <- RegSet) yield {(c->regExpr)}).toMap
    for (TypeAssertion(x, c: Concept) <- ConAstSet) {
      if (RegMap.get(c) != None) {
        var Element = ConceptMap.get(x)
        if (Element == None) ConceptMap += (x -> Set(c))
        else {
          ConceptMap = ConceptMap.updated(x, Element.get + c)
        }
      }
    }
    var ConIterator = ConceptMap.valuesIterator
    var break = false
    while(ConIterator.hasNext && !break) {
      var s = ConIterator.next()
      var RegIterator = s.iterator
      var Con = RegIterator.next()
      var Automata = (new dk.brics.automaton.RegExp(RegMap.get(Con).get)).toAutomaton()
      while(RegIterator.hasNext) {
        Con = RegIterator.next()
        Automata = Automata.intersection((new dk.brics.automaton.RegExp(RegMap.get(Con).get)).toAutomaton())
      }
      if (Automata.isEmpty()) {
        clash = true
        break = true
      }
    }
  }
  
  private def analyzeminCardinality(x: Ind, n: Integer, r: Role, f: Expr) {
    var roleSet: Map[Axiom, Boolean] = Map()
    if (f.equals(Top)) {
      roleSet = axiomMap.filterKeys(e => e match {
      							case RoleAssertion(r, x, _) => true
      							case _ => false})
    } else {
      roleSet = axiomMap.filterKeys(e => e match {
      							case RoleAssertion(r, x, y) => 
      								if (axiomMap.keySet.contains(TypeAssertion(y, f))) true
      								else false
      							case _ => false})
    }
    if (roleSet.size < n) {
        for (i <- 1 to n){
        	val y = nextInd()
        	var s = axiomMap.keySet
        	instanceSet += y
        	//FIXME is it meaningful to check the generated instance are equivalent?
        	axiomMap += (RoleAssertion(r, x, y) -> false)	   	
        	currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
        	if (!f.equals(Top)) {
        	  axiomMap += (TypeAssertion(y, f) -> false)	   	
        	  if (this.tbox != null) axiomMap += (TypeAssertion(y, this.tbox) -> false)	
        	  currentNode = Tree.insert(currentNode, TypeAssertion(y, f))
        	}
        }
    }
    for (TypeAssertion(x, c) <- axiomMap.filterKeys(e => e match {
      															case TypeAssertion(x, ForAll(r, _)) => true
      															case _ => false}).keySet) {
      Tableau(x, c)
    }
  }
  
  private def analyzemaxCardinality(x: Ind, n: Integer, r: Role, f: Expr): Unit = {    
    //FIXME type-casting
    var orSet : Set[RoleAssertion] = Set[RoleAssertion]()
    var oldmap = axiomMap
    var count: Integer = 0
    var roleSet : List[RoleAssertion] = List[RoleAssertion]()
    if (f.equals(Top)) roleSet = axiomMap.filterKeys(e => e match {
      									case RoleAssertion(r, x, _) => true
      									case _ => false
    								}).keySet.toList.asInstanceOf[List[RoleAssertion]]
    else roleSet = axiomMap.filterKeys(e => e match {
      									case RoleAssertion(r, x, y) => axiomMap.keySet.contains(TypeAssertion(y, f))
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
        //update axiomMap by replacing all replacedInd with replaceInd
        var breakflag = false
        var iterator = oldmap.iterator
        while(!breakflag && iterator.hasNext) {//for ( e <- axiomMapbackup){         
          if (checkEqual(instance, replaceInd) ) {
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
        	  			}) && (axiomMap.keySet contains TypeAssertion(replaceInd, nnf(Not(expr))))) {
        	  				clash = true;            	    
        	  				if (result != null)  currentNode.updateValue(TypeAssertion(replaceInd, expr))
            	    //FIXME should break out the for loop
            	    //break;
        	  				breakflag = true
        	  			}
        	  			else {
        	  				axiomMap = axiomMap.-(e._1).+(TypeAssertion(replaceInd, expr) -> false)
        	  				if (result != null)   currentNode.updateValue(TypeAssertion(replaceInd, expr))
        	  			}
        	  		}
        	  	case RoleAssertion(role, ind1, ind2) =>
        	  		var result = currentNode.find(RoleAssertion(role, ind1, ind2))
        	  		if (result != null) currentNode = result
        	  		if (ind1.equals(instance) && ind2.equals(instance)) {
        	  			axiomMap = axiomMap.-(e._1).+(RoleAssertion(role, replaceInd, replaceInd) -> false)
        	  			if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, replaceInd))               
        	  		} else if (ind1.equals(instance)) {
        	  			axiomMap = axiomMap.-(e._1).+(RoleAssertion(role, replaceInd, ind2) -> false)
        	  			if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, ind2))    
        	  		} else if (ind2.equals(instance)) {
        	  			axiomMap = axiomMap.-(e._1).+(RoleAssertion(role, ind1, replaceInd) -> false)
        	  			if (result != null)  currentNode.updateValue(RoleAssertion(role, ind1, replaceInd))   
        	  		}
        	  	case _ => Unit
        	  }
          }
        }
        //check all the possibilities
        if (!clash) model += axiomMap.keySet
        else {count += 1; clash = false}
        axiomMap = oldmap
      }
    }
    if (count == roleSet.size -1 ) clash = true
    else clash = false
    }
  }

  private def analyzeForAll(x: Ind, r: Role, f: Expr): Unit = {
    var s = axiomMap.keySet
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
          axiomMap += (TypeAssertion(e, f) -> false)
          currentNode = Tree.insert(currentNode, TypeAssertion(e, f))
        }
      }
    }
  }

  private def analyzeExists(x: Ind, r: Role, f: Expr): Unit = {
    var s = axiomMap.keySet   
    val y = nextInd()
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
        if (isBlocked(x, y, r, f)) { // y is blocked by x
          model += axiomMap.keySet
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
      allset += (for (TypeAssertion(i, f) <- axiomMap.filterKeys(e => e match {
          													case TypeAssertion(instance, _) => true
          													case _ => false
      								}).keySet) yield {f})
      instance = iterator1.next()
    }
    
    allset += (for (TypeAssertion(i, f) <- axiomMap.filterKeys(e => e match {
          													case TypeAssertion(x, _) => true
          													case _ => false
      								}).keySet) yield {f})
    // to calculate the expressions under the instance node y
    for (TypeAssertion(a, c) ← axiomMap.filterKeys(e => e match {
          							case TypeAssertion(x, ForAll(r,_)) => true
          							case TypeAssertion(x, Exists(r, f)) => true
          							case _ => false
      								}).keySet) {
       c match {
              //case Exists(role, form) ⇒ subset += form ; axiomMap = axiomMap.updated(TypeAssertion(a, c), true)
              case ForAll(r, form) ⇒ subset += form ; axiomMap = axiomMap.updated(TypeAssertion(a, c), true)
              case _                  ⇒ Unit
      }
    }
    subset += f
    axiomMap = axiomMap.updated(TypeAssertion(x, Exists(r, f)), true)
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
    //if not blocked, to add all expressions with instance y into axiomMap
    if (!blocked) {
          currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
          instanceSet += y
          axiomMap += (RoleAssertion(r, x, y) -> false)         
          if (this.tbox != null) { 
        	  currentNode = Tree.insert(currentNode, TypeAssertion(y, this.tbox))
        	  axiomMap += (TypeAssertion(y, this.tbox) -> false)
          }
          for (e ← subset) {
    		  if ((e.isInstanceOf[Concept] || e.isInstanceOf[Not]) && (axiomMap.keySet).contains((TypeAssertion(y, nnf(Not(e)))))){
    		    clash = true
    		    currentNode = Tree.insert(currentNode, TypeAssertion(y, e))
    		    //Tree.insert(currentNode, TypeAssertion(y,Bottom))
    		  } 
    		  else {
    			axiomMap += (TypeAssertion(y, e) -> false)
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
        }) && (axiomMap contains TypeAssertion(x, nnf(Not(element))))) {
          clash = true
          currentNode = Tree.insert(currentNode, TypeAssertion(x, element))
          //Tree.insert(currentNode,TypeAssertion(x, Bottom))
          return Unit
        } else {
          axiomMap += (TypeAssertion(x, element) -> false)
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
  
    
  private def getOrSet(s: Set[Axiom]): Set[TypeAssertion] = {
    val orSet: Set[Axiom] = s.filter(e => e match {
       									case TypeAssertion(_, Or(_)) ⇒ true
       									case _                       ⇒ false 
    								});
    // TODO find other solution than type-casting
    return orSet.asInstanceOf[Set[TypeAssertion]]
  }
  
  //check if these two instances are equal
  private def checkEqual(ind1: Ind, ind2: Ind): Boolean = {
    var equal = true
    notEqInstance.foreach(e => if (Set(ind1,ind2).subsetOf(e)) return false)
    return equal
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
    
  private def checkCardinality(): Boolean = {
    var maxCdnSet = axiomMap.filter(e => (e._1 match {
          									  case TypeAssertion(_, maxCardinality(_, _, _)) => true
          						    		  case _ => false
        								})).keySet
    var minCdnSet = axiomMap.filter(e => (e._1 match {
          									  case TypeAssertion(_, minCardinality(_, _, _)) => true
          						    		  case _ => false
        								})).keySet
    var maxIterator: Iterator[Axiom] = maxCdnSet.iterator
    var minIterator: Iterator[Axiom] = minCdnSet.iterator
    var maxbreak = false
    var minbreak = false
    var Cardinality : TypeAssertion = null
    var CdnExpr : maxCardinality = null
    while (maxIterator.hasNext && !maxbreak) {
      //a rule for expressions such as ≤nR.A ⊓ ≤nR.¬A
      maxIterator.next() match {
        case TypeAssertion(x1, max: maxCardinality) =>
          if (axiomMap.keySet.contains((TypeAssertion(x1, maxCardinality(max.n, max.r, Not(max.f)))))) {
        	  clash = true 
        	  maxbreak = true
          } else {
            //a rule for {((x :≥ mR), (x :≤ nR)} and n < m
            while (minIterator.hasNext && !minbreak) {
              minIterator.next() match {
                case TypeAssertion(x2, min: minCardinality) =>
                  if (min.n > max.n && x1.equals(x2) && max.r.equals(min.r) && max.f.equals(min.f)){
                    clash = true
                    minbreak = true
                    maxbreak = true
                  }
                case _ => Unit
              }
            }
          }
        case _ => Unit
      }
    }
    return clash
  }

}