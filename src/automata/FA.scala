package automata

abstract class FA[Symbol, State, TransitionGoal](
    /** input alphabet (a finite, non-empty set of symbols). */
    val alphabet: Set[Symbol],
    /** a finite, non-empty set of states */
    val Q: Set[State],
    /** is an initial state, an element of S. */
    val q0: State,
    /** is the state-transition function */
    val transition: (Symbol, State) ⇒ TransitionGoal,
    /** is the set of final states, a (possibly empty) subset of S. */
    val F: Set[State]) {

}