package automata;

/** deterministic finite automaton  */
class DFA[Symbol, State](
  alphabet: Set[Symbol],
  Q: Set[State],
  q0: State,
  transition: (Symbol, State) ⇒ State,
  F: Set[State])
    extends FA[Symbol, State, State](alphabet, Q, q0, transition, F) {

  def times[A, B](a: Set[A], b: Set[B]): Set[(A, B)] =
    for (x ← a; y ← b) yield (x, y)
  def ∆[A](a: Set[A]): Set[(A, A)] = for (x ← a) yield (x, x)

  def product[Symbol2, State2](that: DFA[Symbol2, State2]): DFA[(Symbol, Symbol2), (State, State2)] =
    new DFA(
      times(this.alphabet, that.alphabet),
      times(this.Q, that.Q),
      (this.q0, that.q0),
      ((s: (Symbol, Symbol2), q: (State, State2)) ⇒ (this.transition(s._1, q._1), that.transition(s._2, q._2))),
      times(this.F, that.F))

  def intersection[State2](that: DFA[Symbol, State2]): DFA[(Symbol, Symbol), (State, State2)] =
    new DFA(
      ∆(alphabet), // TODO assert this.alphabet == that.alphabet
      times(Q, that.Q),
      (q0, that.q0),
      ((s: (Symbol, Symbol), q: (State, State2)) ⇒ (transition(s._1, q._1), that.transition(s._2, q._2))), // TODO assert q._1 == q._2
      times(F, that.F))

}
