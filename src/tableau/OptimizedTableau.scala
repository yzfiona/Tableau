package tableau

import NNF.nnf
import tableau.Internalization.internalize
import datastructure.NTree
import datastructure.TreeNode
import datastructure.TableauInfoSpec._
import model.Ontology
import dk.brics.automaton.Automaton

class OptimizedTableau {

  private var counter: Int = 0
  private def nextInd(): Ind = { counter += 1; return Ind("x" + counter) }
  //private var instanceSet: Set[Ind] = Set[Ind]()
  //private var notEqInstance : Set[Set[Ind]] = Set[Set[Ind]]()

  //private var clash: Boolean = false
  //private var model = Set[Set[Axiom]]()
  //private var axiomMap: Map[Axiom, Boolean] = Map()
  
  private var tbox : Expr = null
  private var onto : Ontology = null
  
  private var Tree = new NTree()
  private var currentNode : TreeNode = null

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
    return isSatisfiable(internalize(onto.TBox) and expr)
  }

  def isSatisfiable(expr: Expr): (Boolean, Set[Set[Axiom]]) = {
    var axiomMap: Map[Axiom, Boolean] = Map()
    var instanceSet: Set[Ind] = Set[Ind]()
    var notEqInstance : Set[Set[Ind]] = Set[Set[Ind]]()
    var toDo = false
    var nnfExpr = NNF.nnf(expr)
    nnfExpr match {
      case And(c) => if (c.size != 0) toDo = true
      case _ => true
    }
    if (toDo) {
      val instance = nextInd()
      instanceSet += instance
      var axiom = TypeAssertion(instance, And(removeRedudantAnd(nnfExpr)))
      axiomMap += (axiom -> false)
      Tree.insert(axiom)
      currentNode = Tree.getRoot()
    }
 
    if (this.onto != null) {
      for (axiom <- this.onto.ABox) {
        axiomMap += (axiom -> false)
        if (currentNode != null) currentNode = Tree.insert(currentNode, axiom)
        else {
              Tree.insert(axiom)
              currentNode = Tree.getRoot()
        }
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
    val tableauInfo : TableauInfo = (instanceSet, notEqInstance, axiomMap, false, Set[Set[Axiom]](), this.tbox)
    return TableauProof(tableauInfo)
  }

  private def TableauProof(tableauInfo:TableauInfo): (Boolean, Set[Set[Axiom]]) = {
    var instanceSet = getInstanceSet(tableauInfo)
    var newMap = getAxiomMap(tableauInfo)
    var orSet = getOrSet(newMap.filter(e ⇒ e._2 == false).keySet)
    var untestedSet = newMap.filter(e ⇒ e._2 == false)
    var clash = false
    var model = getModel(tableauInfo)
    do {
      for (e ← untestedSet) {
        e._1 match {
          case TypeAssertion(a, Or(c)) ⇒ Unit
          case TypeAssertion(a, maxCardinality(n, r, f)) => Unit
          case TypeAssertion(a, c)     ⇒ 
            val newInfo = Tableau(a, c, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
            newMap = getAxiomMap(newInfo)
          	newMap = newMap.updated(e._1, true)
          	clash = getClash(newInfo) 
          	model = getModel(newInfo)
          	instanceSet = getInstanceSet(newInfo)
          case _ => Unit
        }
      }
      //build the test set which doesn't contain or and maxCardinality
      untestedSet = newMap.filter(e ⇒ e._2 == false && 
    		  					 (e._1 match {
    		  						case TypeAssertion(_, Or(_)) => false
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => false
    		  						case RegExprClass(_,_) => false
    		  						case RoleAssertion(_, _, _) => false
    		  						case _ => true
    		  					 }))
         
      orSet ++= getOrSet(newMap.filter(e ⇒ e._2 == false).keySet)
    } while (untestedSet.size != 0 && !clash)
    //proof or Expr
    if (!clash) {
    	clash = checkCardinality(setAxiomMap(tableauInfo, newMap))
    	if (!clash) {
    		if (orSet.size != 0) {
    			newMap = newMap.updated(orSet.first, true)
    			val Result = analyzeOr(orSet.first, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
    			newMap = getAxiomMap(Result)
    			clash = getClash(Result)
    			model = getModel(Result)
    		}
    		else {
    			untestedSet = newMap.filter(e => e._2 == false && 
        								(e._1 match {
          									  case TypeAssertion(_, maxCardinality(_, _, _)) => true
          						    		  case _ => false
        								}))
        		if (untestedSet.size != 0) {
        			for (TypeAssertion(x, expr: maxCardinality) <- untestedSet.keySet) {
        				val newInfo = analyzemaxCardinality(x, expr.n, expr.r, expr.f, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
        				newMap = getAxiomMap(newInfo)
        				clash = getClash(newInfo)
        				model = getModel(newInfo)
        			}
        		}
    			if(!clash) {
    				untestedSet = newMap.filter(e =>e._1 match {
          									case RegExprClass(_, _) => true
          						    		case _ => false
        							   })
        		if (untestedSet.size != 0) {
        		  clash = getClash(analyzeRegExpr(untestedSet.keySet, setAxiomMap(tableauInfo, newMap)))
        		}
    			}     
    			if (!clash) model += newMap.keySet
    		}
    	}
    }
    if (clash) println("clash")
    else println("model: " + model)
    Tree.print();

    return (clash, model)
  }
     
  private def Tableau(i: Ind, f: Expr, tableauInfo: TableauInfo): TableauInfo = f match {
    case And(expr)    ⇒ analyzeAnd(i, expr, tableauInfo)
    case Exists(r, f) ⇒ analyzeExists(i, r, f, tableauInfo)
    case ForAll(r, f) ⇒ analyzeForAll(i, r, f, tableauInfo)
    case minCardinality(n, r, f) => analyzeminCardinality(i, n, r, f, tableauInfo)
    case Concept(c) => setAxiomMap(tableauInfo, getAxiomMap(tableauInfo).updated(TypeAssertion(i, f), true))
    case Not(Concept(c)) => setAxiomMap(tableauInfo, getAxiomMap(tableauInfo).updated(TypeAssertion(i, f), true))
    case _            ⇒  setAxiomMap(tableauInfo, getAxiomMap(tableauInfo))//println("Error: No matched pattern found")
  }

  private def analyzeOr(or: TypeAssertion, tableauInfo: TableauInfo): TableauInfo = {
    var newMap = getAxiomMap(tableauInfo)
    var instanceSet = getInstanceSet(tableauInfo)
    var andSet: Set[Axiom] = Set[Axiom]()
    var BranchNode = currentNode
    var orSet : Set[TypeAssertion] = Set()
    var clash = false
    var model = getModel(tableauInfo)
    or match {
      case TypeAssertion(a, Or(cs)) =>
      var i = 0
      if (!clash) {
        for (f ← cs) {
        newMap = getAxiomMap(tableauInfo)
        instanceSet = getInstanceSet(tableauInfo)
        andSet = Set(TypeAssertion(a, f)) 
        currentNode = Tree.insert(currentNode, TypeAssertion(a, f))
        clash = false
        do {
          for (a TypeAssertion c ← andSet) {
            if (isClash(a, c, newMap.keySet))  clash = true    	
            else {     
                val newInfo = Tableau(a, c, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
            	newMap = getAxiomMap(newInfo)
            	newMap = newMap.updated(TypeAssertion(a, c), true)
            	clash = getClash(newInfo)
            	model = getModel(newInfo)
            	instanceSet = getInstanceSet(newInfo)
            }
          }
          andSet = newMap.filter(e ⇒ e._2 == false && 
        		  				(e._1 match {
        		  					case TypeAssertion(_, Or(_)) => false
        		  					case TypeAssertion(_, maxCardinality(_, _, _)) => false
        		  					case RoleAssertion(_, _, _) => false
        		  					case _ => true
        		  				})).keySet
        } while (andSet.size != 0 && !clash)
          orSet = getOrSet(newMap.filter(e ⇒ e._2 == false).keySet)
        if (!orSet.isEmpty && !clash) {
          newMap = newMap.updated(orSet.first, true)
          val Result = analyzeOr(orSet.first, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
          newMap = getAxiomMap(Result)
          clash = getClash(Result)
          model = getModel(Result)
          instanceSet = getInstanceSet(tableauInfo)
        } else if (!clash) {
          //to check maxCardinality
          var maxSet = newMap.filter(e => e._1 match {
    		  						case TypeAssertion(_, maxCardinality(_, _, _)) => true
    		  						case _ => false
    		  					}).keySet
    	  clash = checkCardinality(setAxiomMap(tableauInfo, newMap))
          if (maxSet.size == 0) model += newMap.keySet
          else if (!clash){        	    
        	  	var iterator = maxSet.iterator
            	while(!clash && iterator.hasNext) {
            	    val e = iterator.next().asInstanceOf[TypeAssertion]
            	    //FIXME type-casting
            	    val f = e.expr.asInstanceOf[maxCardinality]
            		val newInfo = analyzemaxCardinality(e.a, f.n, f.r, f.f, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
            		newMap = getAxiomMap(newInfo)
            		clash = getClash(newInfo)
            		model = getModel(newInfo)
            		instanceSet = getInstanceSet(tableauInfo)
            	}
          }          
        }
        if (!clash) {
          var untestedSet = newMap.filter(e =>e._1 match {
          									case RegExprClass(_, _) => true
          						    		case _ => false
        							   }).keySet
          if (untestedSet.size != 0) clash = getClash(analyzeRegExpr(untestedSet, setAxiomMap(tableauInfo, newMap)))
        }
        if (clash) i += 1
        //axiomMap = oldmap
        currentNode = BranchNode
       // instanceSet = oldinstanceSet
      }
      if (i == cs.size) clash = true
      else clash = false
      }
    }
    return setResultwithModel(tableauInfo, newMap, clash, model)
  }
  
  private def analyzeRegExpr(RegSet: Set[Axiom], tableauInfo: TableauInfo): TableauInfo = {
    var clash = false
    var ConAstSet = getAxiomMap(tableauInfo).filter(e =>e._1 match {
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
    while(ConIterator.hasNext && !clash) {
      var s = ConIterator.next()
      var RegIterator = s.iterator
      var Con = RegIterator.next()
      var Automata = (new dk.brics.automaton.RegExp(RegMap.get(Con).get)).toAutomaton()
      while(RegIterator.hasNext) {
        Con = RegIterator.next()
        Automata = Automata.intersection((new dk.brics.automaton.RegExp(RegMap.get(Con).get)).toAutomaton())
      }
      if (Automata.isEmpty())	clash = true
    }
    return setClash(tableauInfo, clash)
  }
  
  private def analyzeminCardinality(x: Ind, n: Integer, r: Role, f: Expr, tableauInfo: TableauInfo): TableauInfo = {
    var newMap = getAxiomMap(tableauInfo)
    var model = getModel(tableauInfo)
    var roleSet: Map[Axiom, Boolean] = Map()
    var instanceSet = getInstanceSet(tableauInfo)
    var clash = false
    val tbox = getTBox(tableauInfo)
    if (f == Top) {
      roleSet = newMap.filterKeys(e => e match {
      							case RoleAssertion(r, x, _) => true
      							case _ => false})
    } else {
      roleSet = newMap.filterKeys(e => e match {
      							case RoleAssertion(r, x, y) => 
      								if (newMap.keySet.contains(TypeAssertion(y, f))) true
      								else false
      							case _ => false})
    }
    if (roleSet.size < n) {
        for (i <- 1 to n){
        	val y = nextInd()
        	var s = newMap.keySet
        	instanceSet += y
        	//FIXME is it meaningful to check the generated instance are equivalent?
        	newMap += (RoleAssertion(r, x, y) -> false)	   	
        	currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
        	if (f != Top) {
        	  newMap += (TypeAssertion(y, f) -> false)	   	
        	  if (tbox != null) newMap += (TypeAssertion(y, tbox) -> false)	
        	  currentNode = Tree.insert(currentNode, TypeAssertion(y, f))
        	}
        }
    }
    for (TypeAssertion(x, c) <- newMap.filterKeys(e => e match {
      													case TypeAssertion(x, ForAll(r, _)) => true
      													case _ => false}).keySet) {
      val newInfo = Tableau(x, c, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
      newMap = getAxiomMap(newInfo)
      clash = getClash(newInfo)
      model = getModel(newInfo)
      instanceSet = getInstanceSet(newInfo)
    }
    return setTableauInfo(tableauInfo, newMap, clash, model, instanceSet)
  }
  
  private def analyzemaxCardinality(x: Ind, n: Integer, r: Role, f: Expr, tableauInfo: TableauInfo): TableauInfo = {    
    var clash = false
    var orSet : Set[RoleAssertion] = Set[RoleAssertion]()
    var axiomMap = getAxiomMap(tableauInfo)
    var newMap = axiomMap
    var model = getModel(tableauInfo)
    var count: Integer = 0
    var roleSet : List[RoleAssertion] = List[RoleAssertion]()
    if (f == Top) roleSet = newMap.filterKeys(e => e match {
      									case RoleAssertion(r, x, _) => true
      									case _ => false
    								}).keySet.toList.asInstanceOf[List[RoleAssertion]]
    else roleSet = newMap.filterKeys(e => e match {
      									case RoleAssertion(r, x, y) => newMap.keySet.contains(TypeAssertion(y, f))
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
        var iterator = axiomMap.iterator
        while(!clash && iterator.hasNext) {       
          if (checkEqual(instance, replaceInd, getnotEqInstance(tableauInfo)) ) {
        	  var e = iterator.next()
        	  e._1 match {
        	  	case TypeAssertion(ind, expr) =>
        	  		if (ind == instance) {
        	  			var result = currentNode.find(TypeAssertion(instance, expr))
        	  			if (result != null) currentNode = result
        	  			if ((expr match {
            	  			case Concept(_) ⇒ true
            	  			case Not(_)     ⇒ true
            	  			case _          ⇒ false
        	  			}) && (newMap.keySet contains TypeAssertion(replaceInd, nnf(Not(expr))))) {
        	  				clash = true;            	    
        	  				if (result != null)  currentNode.updateValue(TypeAssertion(replaceInd, expr))
        	  			}
        	  			else {
        	  				newMap = newMap.-(e._1).+(TypeAssertion(replaceInd, expr) -> false)
        	  				if (result != null)   currentNode.updateValue(TypeAssertion(replaceInd, expr))
        	  			}
        	  		}
        	  	case RoleAssertion(role, ind1, ind2) =>
        	  		var result = currentNode.find(RoleAssertion(role, ind1, ind2))
        	  		if (result != null) currentNode = result
        	  		if (ind1 == instance && ind2 ==instance) {
        	  			newMap = newMap.-(e._1).+(RoleAssertion(role, replaceInd, replaceInd) -> false)
        	  			if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, replaceInd))               
        	  		} else if (ind1 == instance) {
        	  			newMap = newMap.-(e._1).+(RoleAssertion(role, replaceInd, ind2) -> false)
        	  			if (result != null) currentNode.updateValue(RoleAssertion(role, replaceInd, ind2))    
        	  		} else if (ind2 == instance) {
        	  			newMap = newMap.-(e._1).+(RoleAssertion(role, ind1, replaceInd) -> false)
        	  			if (result != null)  currentNode.updateValue(RoleAssertion(role, ind1, replaceInd))   
        	  		}
        	  	case _ => Unit
        	  }
          }
        }
        //check all the possibilities
        if (!clash) model += newMap.keySet
        else {count += 1; clash = false}
        newMap = axiomMap
      }
    }
    if (count == roleSet.size -1 ) clash = true
    else clash = false
    }
    return setResultwithModel(tableauInfo, newMap, clash, model)
  }

  private def analyzeForAll(x: Ind, r: Role, f: Expr, tableauInfo: TableauInfo): TableauInfo = {
    var newMap = getAxiomMap(tableauInfo)
    var s = newMap.keySet
    val instanceSet = getInstanceSet(tableauInfo)
    var clash = false
    for (e ← instanceSet) {
      if ((s contains RoleAssertion(r, x, e)) && !(s contains TypeAssertion(e, f))) {
        if (isClash(e, f, s)) {
          clash = true
          currentNode = Tree.insert(currentNode, TypeAssertion(x, f))
          //Tree.insert(currentNode, TypeAssertion(e, Bottom))
          return setResult(tableauInfo, newMap, clash)
        } else {
          newMap += (TypeAssertion(e, f) -> false)
          currentNode = Tree.insert(currentNode, TypeAssertion(e, f))
        }
      }
    }
    return setResult(tableauInfo, newMap, clash)
  }

  private def analyzeExists(x: Ind, r: Role, f: Expr, tableauInfo: TableauInfo): TableauInfo = {
    var newMap = getAxiomMap(tableauInfo)
    var model = getModel(tableauInfo)
    var instanceSet = getInstanceSet(tableauInfo)
    var clash = false
    var s = newMap.keySet   
    val y = nextInd()
    if (!((s contains RoleAssertion(r, x, y)) && (s contains TypeAssertion(y, f)))) {
        val Result = isBlocked(x, y, r, f, setTableauInfo(tableauInfo, newMap, clash, model, instanceSet))
        clash = getClash(Result._1)
        instanceSet = getInstanceSet(Result._1)
        if (!Result._2){
          newMap = getAxiomMap(Result._1)
        } else { // y is blocked by x
          model += newMap.keySet
        }
    }
    return setTableauInfo(tableauInfo, newMap, clash, model, instanceSet)
  }

 
  private def isBlocked(x: Ind, y: Ind, r: Role, f: Expr, tableauInfo: TableauInfo): (TableauInfo,Boolean) = {
    var newMap = getAxiomMap(tableauInfo)
    var instanceSet = getInstanceSet(tableauInfo)
    var blocked = false
    var subset = Set[Expr](f)
    var allset = Set[Set[Expr]]()
    val iterator1 = instanceSet.iterator
    var instance = iterator1.next()
    var clash = false
    val tbox = getTBox(tableauInfo)
    //to check if y is blocked by any of its ancestors
    while (instance != x){
      allset += (for (TypeAssertion(i, f) <- newMap.filterKeys(e => e match {
          													case TypeAssertion(instance, _) => true
          													case _ => false
      								}).keySet) yield {f})
      instance = iterator1.next()
    }
    
    allset += (for (TypeAssertion(i, f) <- newMap.filterKeys(e => e match {
          													case TypeAssertion(x, _) => true
          													case _ => false
      								}).keySet) yield {f})
    // to calculate the expressions under the instance node y
    for (TypeAssertion(a, c) ← newMap.filterKeys(e => e match {
          							case TypeAssertion(x, ForAll(r,_)) => true
          							case TypeAssertion(x, Exists(r, f)) => true
          							case _ => false
      								}).keySet) {
       c match {
              case ForAll(r, form) ⇒ subset += form ; newMap = newMap.updated(TypeAssertion(a, c), true)
              case _                  ⇒ Unit
      }
    }
    subset += f
    newMap = newMap.updated(TypeAssertion(x, Exists(r, f)), true)
    //to check blocking
    val iterator2 = allset.iterator
    while (!blocked && iterator2.hasNext) {
      val xset = iterator2.next()
      if (subset.subsetOf(xset)) { // y is blocked by x
    	  blocked = true    	  
      } 
    }
    //if not blocked, to add all expressions with instance y into axiomMap
    if (!blocked) {
          currentNode = Tree.insert(currentNode, RoleAssertion(r, x, y))
          instanceSet += y
          newMap += (RoleAssertion(r, x, y) -> false)         
          if (tbox != null) { 
        	  currentNode = Tree.insert(currentNode, TypeAssertion(y, tbox))
        	  newMap += (TypeAssertion(y, tbox) -> false)
          }
          for (e ← subset) {
    		  if (isClash(y, e, newMap.keySet)){
    		    clash = true
    		    currentNode = Tree.insert(currentNode, TypeAssertion(y, e))
    		    //Tree.insert(currentNode, TypeAssertion(y,Bottom))
    		  } 
    		  else {
    			newMap += (TypeAssertion(y, e) -> false)
    			currentNode = Tree.insert(currentNode, TypeAssertion(y,e))
    		  }
    	  }
    }
    return (setTableauInfo(tableauInfo, newMap, clash, getModel(tableauInfo), instanceSet), blocked)
  }

  private def analyzeAnd(x: Ind, list: List[Expr], tableauInfo: TableauInfo): TableauInfo = {
    var newMap = getAxiomMap(tableauInfo)
    var clash = false
    for (element ← list) {
        if (isClash(x, element, newMap.keySet)) {
          clash = true
          currentNode = Tree.insert(currentNode, TypeAssertion(x, element))
          //Tree.insert(currentNode,TypeAssertion(x, Bottom))
          return setResult(tableauInfo, newMap, clash)
        } else {
          newMap += (TypeAssertion(x, element) -> false)
          currentNode = Tree.insert(currentNode,TypeAssertion(x, element))
        }
    }
    return setResult(tableauInfo, newMap, clash)
  }
  
  private def isClash(ind: Ind, element: Expr, axiomSet: Set[Axiom]): Boolean = {
    if ((element match {
          case Concept(_) ⇒ true
          case Not(_)     ⇒ true
          case _          ⇒ false
        }) && (axiomSet contains TypeAssertion(ind, nnf(Not(element))))) {
      return true
    } else return false
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
  private def checkEqual(ind1: Ind, ind2: Ind, notEqInstance:  Set[Set[Ind]]): Boolean = {
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
    
  private def checkCardinality(tableauInfo: TableauInfo): Boolean = {
    var clash = false
    val axiomMap = getAxiomMap(tableauInfo)
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
    var Cardinality : TypeAssertion = null
    var CdnExpr : maxCardinality = null
    while (maxIterator.hasNext && !clash) {
      //a rule for expressions such as ≤nR.A ⊓ ≤nR.¬A
      maxIterator.next() match {
        case TypeAssertion(x1, max: maxCardinality) =>
          if (axiomMap.keySet.contains((TypeAssertion(x1, maxCardinality(max.n, max.r, Not(max.f))))))  clash = true 
          else {
            //a rule for {((x :≥ mR), (x :≤ nR)} and n < m
            while (minIterator.hasNext && !clash) {
              minIterator.next() match {
                case TypeAssertion(x2, min: minCardinality) =>
                  if (min.n > max.n && x1 == x2 && max.r == min.r && max.f == min.f)  clash = true
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