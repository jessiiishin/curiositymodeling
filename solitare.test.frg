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
	assert some gs: GameState | gameComplete[gs] is inconsistent with twelve_init
}