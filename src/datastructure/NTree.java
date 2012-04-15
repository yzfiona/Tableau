package datastructure;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;

import tableau.Axiom;

public class NTree {
	private int n;
	private TreeNode root;
	
	public void insert(Axiom value) {
		root = insert(root, value);
	}
	
	public TreeNode insert(TreeNode node, Axiom value){
		if (node == null) {
			node = new TreeNode(value);
			n++;
		} else {
			TreeNode newNode = new TreeNode(value);
			newNode.setParent(node);
			node.getChildren().add(newNode);
			node = newNode;
			n++;
		} 
		return node;
	}
	
	public void print(){
		TreeNode Node = root, AncestorNode = root, EmptyLabel = new TreeNode();
		Queue<TreeNode> Queue = new LinkedList<TreeNode>();  
		Queue.offer(Node);
		Queue.offer(null);
		while (!Queue.isEmpty()) {
			Node = Queue.poll();
			if (Node == null) System.out.println();
			else {
				if (Node.equals(EmptyLabel)) System.out.print("    ");
				else if (Node.getChildren().size() == 0) {
					System.out.print(Node.getValue()+"(leaf) ");
					if (Node.getParent().equals(AncestorNode)) AncestorNode = findNextAncestor(AncestorNode);
				}
				else {
					System.out.print(Node.getValue()+" ");
					for (TreeNode child : Node.getChildren()) {
						if (AncestorNode.getChildren().contains(child.getParent())){
							Queue.offer(null);
							AncestorNode = child.getParent();
						}
						Queue.offer(child);
					}
					Queue.offer(EmptyLabel);
				}
			}
		}
	}
	
	//FIXME
	private TreeNode findNextAncestor(TreeNode AncestorNode) {
		// TODO Auto-generated method stub
		TreeNode NextAncestorNode = AncestorNode, ParentNode = AncestorNode.getParent();
		int count = 0, index = ParentNode.getChildren().indexOf(AncestorNode);
		boolean notFinish = true;
		while(ParentNode.getChildren().size() <= index + 1 && !ParentNode.equals(root)) {
			TreeNode temp = ParentNode;
			ParentNode = ParentNode.getParent();
			index = ParentNode.getChildren().indexOf(temp);
			count++;
		}
		//TreeNode StartNode = ParentNode;
		//int StartIndex = index + 1, DownCount = count;
		notFinish = (index + 1) < ParentNode.getChildren().size();
		while (notFinish) {
			NextAncestorNode = ParentNode.getChildren().get(index + 1);
			count--;
			ParentNode = NextAncestorNode;
			index = 0;
			while(count > 0 && ParentNode.getChildren().size() > 0) {
				NextAncestorNode = ParentNode.getChildren().get(index);
				count--;
				ParentNode = NextAncestorNode;
			}
			if (count <= 0) notFinish = false;
			else {
				while(ParentNode.getChildren().size() <= index + 1 && !ParentNode.equals(root)) {
					TreeNode temp = ParentNode;
					ParentNode = ParentNode.getParent();
					index = ParentNode.getChildren().indexOf(temp);
					count++;
				}
				if (ParentNode.equals(root) && index == ParentNode.getChildren().size() - 1) notFinish = false;
			}
		}
		return NextAncestorNode;
	}

	public TreeNode getRoot(){
		return root;
	}
	
	private void traverse(TreeNode node){
		if (node != null) {
			for (TreeNode child : node.getChildren()) {
				System.out.print(child.getValue());
			}
		}
	}
	

}
