package test;

import static org.junit.Assert.*;

import org.junit.Test;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.RegExp;

public class AutomatonTest {

	@Test
	public void SimpleTest() {
		RegExp r = new RegExp("ab(c|d)*");
		Automaton a = r.toAutomaton();
		String s = "abcccdc";
		assertTrue(a.run(s));
	}
	
	@Test
	public void IntersectionTest() {
		RegExp r1 = new RegExp("ab(c|d)*");
		RegExp r2 = new RegExp("ab*");
		Automaton a = r1.toAutomaton().intersection(r2.toAutomaton());
		String s = "ab";
		assertTrue(a.run(s));
	}
	
	@Test
	public void UnionTest() {
		RegExp r1 = new RegExp("ab(c|d)*");
		RegExp r2 = new RegExp("(c|d)*");
		Automaton a = r1.toAutomaton().union(r2.toAutomaton());
		String s = "cccdc";
		assertTrue(a.run(s));
	}
	
	@Test
	public void ConcatenationTest() {
		RegExp r1 = new RegExp("ab");
		RegExp r2 = new RegExp("(c|d)*");
		Automaton a = r1.toAutomaton().concatenate(r2.toAutomaton());
		String s = "abcccdc";
		assertTrue(a.run(s));
	}
	
	@Test
	public void EmptyTest() {
		RegExp r1 = new RegExp("ab");
		RegExp r2 = new RegExp("(c|d)*");
		Automaton a = r1.toAutomaton().intersection(r2.toAutomaton());
		String s = "abcccdc";
		assertTrue(a.isEmpty());
	}
	
	@Test
	public void ComplementTest() {
		RegExp r = new RegExp("(c|d)*");
		Automaton a = r.toAutomaton().complement();
		String s = "abcccdc";
		assertTrue(a.run(s));
	}
	
	@Test
	public void RepeatTest() {
		RegExp r = new RegExp("ab(c|d)*");
		Automaton a = r.toAutomaton().repeat();
		String s = "abcccdcabab";
		assertTrue(a.run(s));
	}
	
	@Test
	public void MinusTest() {
		RegExp r1 = new RegExp("ab(c|d)*");
		RegExp r2 = new RegExp("cd");
		Automaton a = r1.toAutomaton().minus(r2.toAutomaton());
		String s = "ab";
		assertTrue(a.run(s));
	}

}
