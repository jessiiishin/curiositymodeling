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
            inPile[gs, p1, c]
            inPile[gs, p2, c]
        }
    }
}

// card is in multiple endpiles at once
pred cardInMultipleEndPiles {
    some gs: GameState, c: Card | {
        some disj ep1, ep2: EndPile | {
            inEndPile[gs, ep1, c]
            inEndPile[gs, ep2, c]
        }
    }
}

pred cardInDeckAndDiscard {
    some gs: GameState, c: Card | {
        some dis: Discard | inDiscard[gs, c]
        some deck: Deck | inDeck[gs, c]
    }
}

// how to make it more efficient?
pred cardInMultiplePlaces {
    some gs: GameState, c: Card, p: Pile, ep: EndPile, d: Deck | {
        (inPile[gs, p, c] and inEndPile[gs, ep, c]) or 
        (inPile[gs, p, c] and inDeck[gs, c]) or 
        (inEndPile[gs, ep, c] and inDeck[gs, c]) 
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
        inEndPile[gs, ep, c]
        gs.faceDown[c] = True
    }
}

pred cardFaceDownInDiscard {
    some gs: GameState, c: Card, dis: Discard | {
        inDiscard[gs, c]
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
        #{c: Card | inPile[gs, p, c] and
            gs.faceDown[c] = False} > 1
    }
}

// endpiles always include all the ranks when complete (for twelve cards)
pred endPilesWithAllRanks {
    some gs: GameState | {
        all ep: EndPile | {
            gs.endPileTop[ep].rank = 3
            gs.cardBelow[endPileTop[ep]].rank = 2
            gs.cardBelow[cardBelow[endPileTop[ep]]].rank = 1
        }
    }
    
}

// face down cards dont need to have color alternation and also doesn't need to be in order
pred faceDownCardsNoColorAlt {
    some p: Pile, gs: GameState | {
        some disj c1, c2: Card | {
            gs.faceDown[c1] = True
            gs.faceDown[c2] = True
            c1.color = c2.color
            gs.cardBelow[c1] = c2
            inPile[gs, p, c1]
            inPile[gs, p, c2]
        }
    }
}

pred faceDownCardsNoRankOrder {
    some p: Pile, gs: GameState | {
        some disj c1, c2: Card | {
            gs.faceDown[c1] = True
            gs.faceDown[c2] = True
            c1.rank >= c2.rank
            gs.cardBelow[c1] = c2
            inPile[gs, p, c1]
            inPile[gs, p, c2]
        }
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
    GW_noColorAltStillWellformed: assert {}

    GW_sameCards: assert {some disj c1, c2: Card | c1.suit = c2.suit and c1.rank = c2.rank and general_wellformed} is unsat
    GW_sameSuit: assert {some disj c1, c2: Card | c1.suit = c2.suit and general_wellformed} is sat for exactly 12 Card
    GW_sameRank: assert {some disj c1, c2: Card | c1.rank = c2.rank and general_wellformed} is sat
    
    GW_dontNeedTwelveWellformed: assert {not twelve_wellformed and general_wellformed} is sat
}

test suite for twelve_wellformed {
    TW_noCardsOutOfRange: assert {some c: Card | (c.rank > 3 or c.rank < 1) and twelve_wellformed} is unsat
    TW_consistentWithGeneral: assert twelve_wellformed is consistent with general_wellformed
    TW_cardInRange: assert {some c: Card | c.rank = 1 or c.rank = 2 or c.rank = 3 and twelve_wellformed} is sat
    TW_cardRankZero: assert {some c: Card | c.rank = 0 and twelve_wellformed} is unsat

}

test suite for wellformed_initial {
    // WI_consistentWithGeneral: assert general_wellformed is consistent with wellformed_initial

}

test suite for twelve_init {
	// we cannot be init stage and be complete
	assert some gs: GameState | gameComplete[gs] is inconsistent with twelve_init
}

test suite for exclusiveDecksAndPiles {
    
}




/* 
--------------------------------------------------
    Predicates for valid moves
--------------------------------------------------
*/

pred nothingChanges[pre, post: GameState] {
    pre.deckTop = post.deckTop
    pre.discardTop = post.discardTop
    all p: Pile | pre.columnTop[p] = post.columnTop[p]
    all ep: EndPile | pre.endPileTop[ep] = post.endPileTop[ep]
    all c: Card | pre.cardBelow[c] = post.cardBelow[c]
    all c: Card | pre.faceDown[c] = post.faceDown[c]
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