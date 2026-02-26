#lang forge

open "solitare.frg"

/* 
--------------------------------------------------
    Predicates related to card wellformedness
    andtheir memberships
--------------------------------------------------
*/

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

// card is in multiple piles at once
pred cardInMultPiles {
    some gs: GameState, c: Card | {
        some disj p1, p2: Pile | {
            cardInPile[c, gs, p1]
            cardInPile[c, gs, p2]
        }
    }
}

// card is in multiple endpiles at once
pred cardInMultipleEndPiles {
    some gs: GameState, c: Card | {
        some disj ep1, ep2: EndPile | {
            cardInEndPile[c, gs, ep1]
            cardInEndPile[c, gs, ep2]
        }
    }
}

pred cardInDeckAndDiscard {
    some gs: GameState, c: Card | {
        some dis: Discard | cardInDiscard[c, gs, dis]
        some deck: Deck | cardInDeck[c, gs, deck]
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

pred cardFaceDownInDiscard {
    some gs: GameState, c: Card, dis: Discard | {
        cardInDiscard[c, gs, dis]
        gs.faceDown[c] = True
    }
}

// card is at top of pile but is also below some other card
pred topCardButBelow {
    some gs: GameState | {
        some disj c1, c2: Card | {
            some p: Pile, ep: EndPile, d: Deck | {
                gs.cardBelow[c2, c1] and
                (c1 = gs.columnTop[p] or
                    c1 = gs.endPileTop[ep] or 
                    c1 = gs.deckTop[d])
            }
        }
    }
}

// multiple cards are face up in one pile at initial
// multiple cards are face up in a state that's not initial
pred multCardsInPileFaceUp {
    some gs: GameState, p: Pile | {
        #{c: Card | cardInPile[c, gs, p] and
            gs.faceDown[c] = False} > 1
    }
}

/* 
--------------------------------------------------
    Suites for wellformed & card memberships
--------------------------------------------------
*/

test suite for general_wellformed {
    // 
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
--------------------------------------------------
    Predicates for valid moves
--------------------------------------------------
*/


/* 
--------------------------------------------------
    Suites for valid moves
--------------------------------------------------
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