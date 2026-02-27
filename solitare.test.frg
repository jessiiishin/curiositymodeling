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

// all cards should be somewhere
pred cardsAreSomewhere {
    some gs: GameState | {
        all c: Card | {
            (some p: Pile | inPile[gs, p, c]) or
            (some ep: EndPile | inEndPile[gs, ep, c]) or
            inDeck[gs, c] or
            inDiscard[gs, c]
        }
    } 
}

// card that's not part of any stack
pred lostCard {
    some gs: GameState | {
        some c: Card | {
            (all p: Pile | not inPile[gs, p, c]) and
            (all ep: EndPile | not inEndPile[gs, ep, c]) and
            not inDeck[gs, c] and
            not inDiscard[gs, c]
        }
    }
}

/* 
--------------------------------------------------
    Suites for wellformed & card memberships
--------------------------------------------------
*/

test suite for general_wellformed {
    // basic card logic
    GW_noCycles: assert {cyclicCards and general_wellformed} is unsat
    GW_unevenSuite: assert {unevenDistributionOfCardsInSuit and general_wellformed} is unsat
    GW_illegalCards: assert {illegalCards and general_wellformed} is unsat
    GW_topButBelow: assert {topCardButBelow and general_wellformed} is unsat

    // card membership
    GW_notExclusiveDeckDiscard: assert {cardInDeckAndDiscard and general_wellformed} is unsat
    GW_notExclusiveEndPile: assert {cardInMultipleEndPiles and general_wellformed} is unsat
    GW_notExclusive: assert {cardInMultiplePlaces and general_wellformed} is unsat
    GW_exclusivity: assert cardsAreSomewhere is necessary for general_wellformed
    GW_lostCard: assert {lostCard and general_wellformed} is unsat

    // game rules related
    GW_noColorAltStillWellformed: assert {faceDownCardsNoColorAlt and general_wellformed} is sat
    GW_noNumberOrderStillWellformed: assert {faceDownCardsNoRankOrder and general_wellformed} is sat
    GW_multiIPileFaceup: assert {multCardsInPileFaceUp and general_wellformed} is sat

    // duplicates?
    GW_sameCards: assert {some disj c1, c2: Card | c1.suit = c2.suit and c1.rank = c2.rank and general_wellformed} is unsat
    GW_sameSuit: assert {some disj c1, c2: Card | c1.suit = c2.suit and general_wellformed} is sat for exactly 12 Card
    GW_sameRank: assert {some disj c1, c2: Card | c1.rank = c2.rank and general_wellformed} is sat for exactly 12 Card
    
    GW_dontNeedTwelveWellformed: assert {not twelve_wellformed and general_wellformed} is sat
}

test suite for twelve_wellformed {
    TW_noCardsOutOfRange: assert {some c: Card | (c.rank > 3 or c.rank < 1) and twelve_wellformed} is unsat
    TW_consistentWithGeneral: assert twelve_wellformed is consistent with general_wellformed
    TW_cardInRange: assert {some c: Card | c.rank = 1 or c.rank = 2 or c.rank = 3 and twelve_wellformed} is sat
    TW_cardRankZero: assert {some c: Card | c.rank = 0 and twelve_wellformed} is unsat
}

test suite for wellformed_initial {
    assert {some gs: GameState | gameComplete[gs] and wellformed_initial} is unsat
    assert {cyclicCards and wellformed_initial} is unsat
    WI_multiIPileFaceup: assert {multCardsInPileFaceUp and wellformed_initial} is unsat
    WI_multiplePlaces: assert {cardInMultiplePlaces and wellformed_initial} is unsat
    WI_topButBelow: assert {topCardButBelow and wellformed_initial} is unsat

    // WI_consistentWithGeneral: assert general_wellformed is consistent with wellformed_initial

}

test suite for twelve_init {
	// we cannot be init stage and be complete
	assert {some gs: GameState | gameComplete[gs] and twelve_init} is unsat
    
}

test suite for exclusiveDecksAndPiles {
    
}

test suite for winnable {
    example unwinnableCase is {not winnable} for {
        `Solitaire0.init = `GS0

        Boolean = `True + `False
        True = `True
        False = `False

        Suit = `Heart + `Diamond + `Spade + `Clover
        Heart = `Heart
        Diamond = `Diamond
        Spade = `Spade
        Clover = `Clover

        Color = `Red + `Black
        Red = `Red
        Black = `Black
        
        -- Cards
        Card = `C1H + `C2H + `C3H + `C1D + `C2D + `C3D + 
            `C1S + `C2S + `C3S + `C1C + `C2C + `C3C

        `C1H.suit = `Heart    `C1H.color = `Red    `C1H.rank = 1
        `C2H.suit = `Heart    `C2H.color = `Red    `C2H.rank = 2
        `C3H.suit = `Heart    `C3H.color = `Red    `C3H.rank = 3
        `C1D.suit = `Diamond  `C1D.color = `Red    `C1D.rank = 1
        `C2D.suit = `Diamond  `C2D.color = `Red    `C2D.rank = 2
        `C3D.suit = `Diamond  `C3D.color = `Red    `C3D.rank = 3
        `C1S.suit = `Spade    `C1S.color = `Black  `C1S.rank = 1
        `C2S.suit = `Spade    `C2S.color = `Black  `C2S.rank = 2
        `C3S.suit = `Spade    `C3S.color = `Black  `C3S.rank = 3
        `C1C.suit = `Clover   `C1C.color = `Black  `C1C.rank = 1
        `C2C.suit = `Clover   `C2C.color = `Black  `C2C.rank = 2
        `C3C.suit = `Clover   `C3C.color = `Black  `C3C.rank = 3

        -- Piles
        Pile = `Pile0 + `Pile1 + `Pile2
        `GS0.columnTop = `Pile0 -> `C2D + 
                         `Pile1 -> `C2S + 
                         `Pile2 -> `C2H

        -- cardBelow chains
        `GS0.cardBelow = `C3H -> `C3D +
                         `C3D -> `C3S +
                         `C3S -> `C1C +
                         `C1C -> `C2C +
                         `C2C -> `C3C +
                         `C2S -> `C1S + 
                         `C2H -> `C1H + 
                         `C1H -> `C1D

        -- faceDown
        `GS0.faceDown = `C2D -> `False +
                        `C2S -> `False +
                        `C1S -> `True  +
                        `C2H -> `False +
                        `C1H -> `True  +
                        `C1D -> `True  +
                        `C3H -> `True  +
                        `C3D -> `True  +
                        `C3S -> `True  +
                        `C1C -> `True  +
                        `C2C -> `True  +
                        `C3C -> `True

        -- Deck
        `GS0.deckTop = `C3H

        -- Discard empty
        no `GS0.discardTop

        -- EndPiles
        EndPile = `EP_Heart + `EP_Diamond + `EP_Spade + `EP_Clover
        `EP_Heart.endPileSuit   = `Heart
        `EP_Diamond.endPileSuit = `Diamond
        `EP_Spade.endPileSuit   = `Spade
        `EP_Clover.endPileSuit  = `Clover
        no `GS0.endPileTop

        -- Solitaire trace
        GameState = `GS0
    }
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

pred moveFromEndPileToEndPile {
    some pre, post: GameState | {
        some disj ep1, ep2: EndPile | pre.endPileTop[ep1] != post.endPileTop[ep2]
    }
}

// two or more cards turned facedown=False
pred twoCardsTurnedFaceUp {
    some disj pre, post: GameState | {
        some disj c1, c2: Card | {
            pre.faceDown[c1] = True
            post.faceDown[c1] = False

            pre.faceDown[c2] = True
            post.faceDown[c2] = False
        }
    }
}

// a card that was face up became facedown = True
pred faceUpToDown {
    some disj pre, post: GameState | {
        some c: Card | {
            pre.faceDown[c] = False
            post.faceDown[c] = True
        }
    }
}

// order of pile changed when card is faceDown
pred faceDownOrderChanged {
    some disj pre, post: GameState | {
        some c: Card | {
            pre.faceDown[c] = True
            post.faceDown[c] = True
            pre.cardBelow[c] != post.cardBelow[c]
        }
    }
}

// unchanged stacks of cards stay the same before and after (contents, order, top)
pred unchangedPilesConsistent[changed: Pile] {
    
}

// two or more cards moved at once
pred 

// a card that was not supposed to be turned face up became face up (not at top or not revealed by deck)


// somehow the color alternation is not correct after a move
// trying to move cards from empty stacks should not be possible

// nothing happened but didn't lose (something should happen at every move)

// not all cards were face up but somehow won
// not all endPiles are complete but somehow won
// not all piles are empty but somehow won


/* 
--------------------------------------------------
    Suites for valid moves
--------------------------------------------------
*/

// card moved to invalid position where it's not wellformed anymore
// card moved from one endpile to another

test suite for validMove {
    assert all pre, post: GameState | validMove[pre, post] is consistent with moveFromEndPileToEndPile
    assert {some pre, post: GameState | nothingChanges and validMove[pre, post]} is unsat
    
}

