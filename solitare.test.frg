#lang forge

open "solitare.frg"

pred cyclicStack {
    
}

test suite for general_wellformed {

}

test suite for twelve_wellformed {
    
}

test suite for wellformed_initial {
    
}

test suite for twelve_init {
	// we cannot be init stage and be complete
    not_finished: assert some gs: GameState | {
		twelve_init and twelve_wellformed and gameComplete[gs]
	} is unsat
}