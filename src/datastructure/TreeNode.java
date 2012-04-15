package datastructure;

import java.util.ArrayList;
import tableau.Axiom;

public class TreeNode{
	private Axiom value;
	private TreeNode parent;
	private ArrayList<TreeNode> children;
	
	public TreeNode(){}
	
	public TreeNode(Axiom value){
		this.value = value;
		children = new ArrayList<TreeNode>();
	}
	
	public TreeNode find(Axiom value){
		TreeNode node = null;
		if (this.value.equals(value)) node = this;
		else {
			for (TreeNode child: children) {
				if (child.find(value) != null) {
					node = child;
					break;
				}
			}
			if (node == null) {
				node = this.parent;
				do {
					if (node == null || node.value.equals(value)) break;
					else node = node.parent;
				} while (node != null);
			}
		}
		return node;
	}
	
	public ArrayList<TreeNode> getChildren(){
		return this.children;
	}
	
	public Axiom getValue(){
		return this.value;
	}
	
	public void updateValue(Axiom value) {
		this.value = value;
	}
	
	public void setParent(TreeNode node){
		this.parent = node;
	}
	
	public TreeNode getParent(){
		return this.parent;
	}
	
}
