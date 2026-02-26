#lang forge

open "solitare.frg"

fun cardInPile[c: Card, gs: GameState, p: Pile]: Boolean {
    (c = gs.columnTop[p]) or (c in gs.columnTop[p].^(gs.cardBelow))
}

fun cardInEndPile[c: Card, gs: GameState, ep: EndPile]: Boolean {
    (c = gs.endPileTop[ep]) or (c in gs.endPileTop[ep].^(gs.cardBelow))
}

fun cardInDeck[c: Card, gs: GameState, d: Deck]: Boolean {
    (c = gs.deckTop[d]) or (c in gs.deckTop[d].^(gs.cardBelow))
}

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
pred cardInMultPiles {
    some gs: GameState, c: Card | {
        some disj p1, p2: Pile | {
            cardInPile[c, gs, p1]
            cardInPile[c, gs, p2]
        }
    }
}

pred cardInMultipleEndPiles {
    some gs: GameState, c: Card | {
        some disj p1, p2: Pile | {
            cardInEndPile[c, gs, p1]
            cardInEndPile[c, gs, p2]
        }
    }
}

// how to make it more efficient?
pred cardInMultiplePlaces {
    some gs: GameState, c: Card, p: Pile, ep: EndPile, d: Deck | {
        (cardInPile[c, gs, p] and cardInEndPile[c, gs, ep]) or 
        (cardInPile[c, gs, p] and cardInDeck[c, gs, d]) or 
        (cardInEndPile[c, gs, ep] and cardInDeck[c, gs, d]) 
    }
}


// is at top of pile but is facedown
pred topCardFaceDown {
    some gs: GameState, c: Card, p: Pile | {
        c = gs.columnTop[p]
        gs.faceDown[c] = True
    }
}

pred cardFaceDownInEndPile {
    some gs: GameState, c: Card, ep: EndPile | {
        cardInEndPile[c, gs, ep]
        gs.faceDown[c] = True
    }
}

// card is at top of pile but is also below some other card
pred topCardButBelow {
    some gs: GameState, disj c1, c2: Card, p: Pile, ep: Pile, d: Deck | {
        gs.cardBelow[c2, c1] and
        (c1 = gs.columnTop[p] or
            c1 = gs.endPileTop[ep] or 
            c1 = gs.deckTop[ep])
    }
}

// multiple cards are face up in one pile at initial
// multiple cards are face up in a state that's not initial
pred multCardsInPileFaceUp {
    some gs: GameState, p: Pile | {
        #{c: Card | cardInPile[c, gs, p]
            gs.faceDown[c] = False} > 1
    }
}

// cards are in the discard or endpile at initial

// multiple cards are top
pred multTopCards {
    some disj c1, c2: Card, gs: GameState | {
        (some p: Pile | gs.columnTop[p] = c1 and gs.columnTop[p] = c2) or
        (some ep: EndPile | gs.endPileTop[p] = c1 and gs.endPileTop[p] = c2) or
        (some d: Deck | gs.deckTop[p] = c1 and gs.deckTop[p] = c2)
    }
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