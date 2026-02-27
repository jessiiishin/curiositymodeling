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

pred unevenDistributionOfCardsInSuit {
    some disj s1, s2: Suit | {
        #{c: Card | c.suit = s1} != #{c: Card | c.suit = s2}
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
            inPile[c, gs, p1]
            inPile[c, gs, p2]
        }
    }
}

// card is in multiple endpiles at once
pred cardInMultipleEndPiles {
    some gs: GameState, c: Card | {
        some disj ep1, ep2: EndPile | {
            inEndPile[c, gs, ep1]
            inEndPile[c, gs, ep2]
        }
    }
}

pred cardInDeckAndDiscard {
    some gs: GameState, c: Card | {
        some dis: Discard | inDiscard[c, gs, dis]
        some deck: Deck | inDeck[c, gs, deck]
    }
}

// how to make it more efficient?
pred cardInMultiplePlaces {
    some gs: GameState, c: Card, p: Pile, ep: EndPile, d: Deck | {
        (inPile[c, gs, p] and inEndPile[c, gs, ep]) or 
        (inPile[c, gs, p] and inDeck[c, gs, d]) or 
        (inEndPile[c, gs, ep] and inDeck[c, gs, d]) 
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
        inEndPile[c, gs, ep]
        gs.faceDown[c] = True
    }
}

pred cardFaceDownInDiscard {
    some gs: GameState, c: Card, dis: Discard | {
        inDiscard[c, gs, dis]
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
        #{c: Card | inPile[c, gs, p] and
            gs.faceDown[c] = False} > 1
    }
}

/* 
--------------------------------------------------
    Suites for wellformed & card memberships
--------------------------------------------------
*/

test suite for general_wellformed {
    GW_noCycles: assert {cyclicCards and general_wellformed} is unsat
    GW_unevenSuite: assert {unevenDistributionOfCardsInSuit and general_wellformed} is unsat
    GW_illegalCards: assert {illegalCards and general_wellformed} is unsat
    GW_notExclusiveDeckDiscard: assert {cardInDeckAndDiscard and general_wellformed} is unsat
    GW_notExclusiveEndPile: assert {cardInMultipleEndPiles and general_wellformed} is unsat
    GW_notExclusive: assert {cardInMultiplePlaces and general_wellformed} is unsat

    GW_sameCards: assert {some disj c1, c2: Card | c1.suit = c2.suit and c1.rank = c2 rank and general_wellformed} is unsat
    GW_sameSuit: assert {some disj c1, c2: Card | c1.suit = c2.suit and general_wellformed} is sat
    GW_sameRank: assert {some disj c1, c2: Card | c1.rank = c2.rank and general_wellformed} is sat

    GW_dontNeedTwelveWellformed: assert {not twelveWellformed and general_wellformed} is sat
}

test suite for twelve_wellformed {
    TW_noCardsOutOfRange: assert {some c: Card | (c.rank > 3 or c.rank < 1) and twelve_wellformed} is unsat
    TW_consistentWithGeneral: assert twelve_wellformed is consistent with general_wellformed
    TW_cardInRange: assert {some c: Card | c.rank = 1 or c.rank = 2 or c.rank = 3 and twelve_wellformed} is sat
    TW_cardRankZero: assert {some c: Card | c.rank = 0 and twelve_wellformed} is unsat

}

test suite for wellformed_initial {
    WI_consistentWithGeneral: assert general_wellformed is consistent with wellformed_initial

}

test suite for twelve_init {
	// we cannot be init stage and be complete
    TI_notComplete: assert { some gs: GameState | gameComplete[gs] and twelve_init[gs] } is unsat
}


// test that endpiles always include all the ranks when complete
// face down cards dont need to have color alternation and also doesn't need to be in order


/* 
--------------------------------------------------
    Predicates for valid moves
--------------------------------------------------
*/

pred nothingChanges {
    some pre, post: GameState | {
        all p: Pile, c: Card | 
    }
}


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
// unchanged stacks of cards stay the same before and after (contents, order, top)
// a card that was not supposed to be turned face up became face up (not at top or not revealed by deck)
// somehow the color alternation is not correct after a move
// trying to move cards from empty stacks should not be possible

// nothing happened but didn't lose (something should happen at every move)

// not all cards were face up but somehow won
// not all endPiles are complete but somehow won
// not all piles are empty but somehow won