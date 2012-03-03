package automata

class NFA[Symbol, State](
  alphabet: Set[Symbol],
  Q: Set[State],
  q0: State,
  transition: (Symbol, State) ⇒ State,
  F: Set[State])
    extends FA[Symbol, State, State](alphabet, Q, q0, transition, F) {

  def toDFA(): DFA[Symbol, State] = null
}