#lang forge

open "solitare.frg"

pred cyclicCards {
    some gs: GameState, c: Card | {
        reachable[c, c, gs.cardBelow]
    }
}

pred illegalCards {
    // suit and color don't match
    some c: Card | {
        (c.color = Red and (c.suit = Spade or c.suit = Clover)) or
        (c.color = Black and (c.suit = Heart or c.suit = Diamond))
    }

    // fields missing
    some c: Card | {
        no c.color or 
        no c.rank or 
        no c.suit
    }

    // negative rank
    some c: Card | {
        c.rank < 0
    }
}

// card is in multiple places at once
pred cardInMultPiles | {
    some gs: GameState, c: Card | {
        some disj p1, p2: Pile | {
            
        }
    }
}

// is at top of pile but is facedown

// card is at top of pile but is also below some other card

// multiple cards are faceup in the pile at initial

// cards are in the discard or endpile at initial

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


/*
Move Tests
*/

// card moved to invalid position where it's not wellformed anymore
// card moved from one endpile to another
// two or more cards moved at once
// two or more cards turned facedown=False
// a card that was face up became facedown = True
// order of pile changed (or endpile, or deck)
// a card that was not supposed to be turned face up became face up (not at top or not revealed by deck)
// somehow the color alternation is not correct after a move

// nothing happened but didn't lose (something should happen at every move)

// not all cards were face up but somehow won
// not all endPiles are complete but somehow won
// not all piles are empty but somehow won