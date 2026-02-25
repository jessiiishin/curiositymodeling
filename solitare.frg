#lang forge

option run_sterling "layout.cnd"

/*
Things to possibly implement

when are cards stackable?:
- alternating colors
- in order of rank, never out of order

when are cards stackable in the complete pile?:
- same suit
- ascending rank order

what can go in empty space:
- only cards that are of rank King when player movement
- any card that is face down in beginning of game

what can player do:
- move card (onto other cards)
- draw card from deck
- reveal card from deck
- move to complete pile

what is a wellformed deck of cards (usually):
- 52 cards
- 13 of each suit: heart, diamond, spade, clover
- all suits have complete set of cards ace through king
    - no other numbers should exist
    - none of them should be duplicates
- cards once game starts preserves their identity
    - doesn't suddenly change their suit, etc.

what is a wellformed game state:
- 7 spaces for cards (each col has 1 card facing up initially)
    - initial state:
    - 1) 1 card
    - 2) 1 card down, 1 card up
    - 3) 2 card down
    - 4) 3 card down
    - 5) ...
- no cards other than the card that was moved by player changes?
    - well except for when the bottom face down cards are revealed
- 
*/

abstract sig Boolean {}
one sig True, False extends Boolean {}
abstract sig Suit {}
abstract sig Color {}
one sig Red, Black extends Color {}
one sig Heart, Diamond, Spade, Clover extends Suit {}

sig GameState {
    init: lone GameState,
    nextState: lone GameState,

    deckTop: pfunc Deck -> Card,
    endPileTop: pfunc EndPile -> Card,
    columnTop: pfunc Pile -> Card, // top of stack
    
    faceDown: func Card -> Boolean,
    cardBelow: pfunc Card -> Card,

    endPileComplete: func EndPile -> Boolean,
    pileEmpty: func Pile -> Boolean,

    // define next and prev in gamestate
    deckEmpty: func Deck -> Boolean
}
// if gamestate is what changes cards next and prev will not change

sig Card {
    suit: one Suit,
    color: one Color,
    rank: one Int
}

sig Pile {}
sig EndPile {
    endPileSuit: one Suit
}
sig Deck {}

pred general_wellformed {
    // each suit has same number of cards
    all disj s1, s2: Suit | {
        #{c: Card | c.suit = s1} = #{c: Card | c.suit = s2}
    }

    // color <-> suit relationship
    all c: Card | {
        (c.suit = Heart or c.suit = Diamond) iff (c.color = Red)
        (c.suit = Spade or c.suit = Clover) iff (c.color = Black)
    }

    // # of endpile = # of suits ?
    all s: Suit | {
        one endPile: EndPile | endPile.endPileSuit = s
    }

    // linearity of stack
    all st: GameState | {
        all c1: Card {
            not st.cardBelow[c1] = c1
            not reachable[c1, c1, st.cardBelow]
        }

        // prevent dags
        all disj c1, c2: Card | {
            some st.cardBelow[c1] and some st.cardBelow[c2] implies {
                st.cardBelow[c1] != st.cardBelow[c2]
            }
        }

        exclusiveDecksAndPiles[st]

        all p: Pile, ep: EndPile | {
            st.pileEmpty[p] = True iff st.columnTop[p] = none
        }
        // if a pile or endPile or deck is not empty, then it must have at least one card that it can reach
    }

}

pred exclusiveDecksAndPiles[st: GameState] {
    all c: Card | {
        let inPile = (some p: Pile | {st.columnTop[p] = c or reachable[c, st.columnTop[p], st.cardBelow]}) |
        let inEndPile = (some ep: EndPile | {st.endPileTop[ep] = c or reachable[c, st.endPileTop[ep], st.cardBelow]}) |
        let inDeck = (some d: Deck | {st.deckTop[d] = c or reachable[c, st.deckTop[d], st.cardBelow]}) | {
            inPile or inEndPile or inDeck

            (inPile implies not inEndPile and not inDeck)
            (inEndPile implies not inPile and not inDeck)
            (inDeck implies not inPile and not inEndPile)
        }
    }
}

/*
12 cards:
- 1, 2, 3 in each suit
- four suits

-> 3 piles with 1, 2, 3 cards, 6 cards in deck
*/
pred twelve_wellformed {
    general_wellformed
    // card ranking is limited to 1 to 3
    all c: Card | c.rank >= 1 and c.rank <= 3
    all disj c1, c2: Card | not (c1.suit = c2.suit and c1.rank = c2.rank) 
}

pred wellformed_initial[gs: GameState] {
    // all piles should be full
    // top of stack has face up, everything else has face down
    all p: Pile | {
        gs.pileEmpty[p] = False
        some gs.columnTop[p]
        gs.faceDown[gs.columnTop[p]] = False

        all c: Card | {
            (reachable[c, gs.columnTop[p], gs.cardBelow] and c != gs.columnTop[p]) implies {
                gs.faceDown[c] = True
            }
        }
    }

    // deck should not be empty and all cards are face down
    all d: Deck | {
        gs.deckEmpty[d] = False
        some gs.deckTop[d]
        all c: Card | (gs.deckTop[d] = c or reachable[c, gs.deckTop[d], gs.cardBelow]) implies {
            gs.faceDown[c] = True
        }
    }

    // endpiles are empty & not complete
    all endPile: EndPile | { 
        gs.endPileComplete[endPile] = False
        no gs.endPileTop[endPile]
    }
}

pred twelve_init {
    some gs: GameState | {
        some disj p1, p2, p3: Pile | {
            no gs.cardBelow[gs.columnTop[p1]]

            (some gs.cardBelow[gs.columnTop[p2]] and 
                no gs.cardBelow[gs.cardBelow[gs.columnTop[p2]]])

            (some gs.cardBelow[gs.columnTop[p3]] and 
                some gs.cardBelow[gs.cardBelow[gs.columnTop[p3]]] and 
                no gs.cardBelow[gs.cardBelow[gs.cardBelow[gs.columnTop[p3]]]])
        }

        some d: Deck | {
            #{c: Card | reachable[c, gs.deckTop[d], gs.cardBelow]} = 5
        }

        wellformed_initial[gs]
    }
}

twelve_cards: run {
    twelve_wellformed 
} for exactly 12 Card, 0 GameState

twelve_cards_wellformed_deal: run {
    twelve_wellformed
    twelve_init
} for exactly 12 Card, exactly 1 GameState, exactly 3 Pile, exactly 4 EndPile, exactly 1 Deck



/*
Card stack properties related predicates
*/

pred isLowerRankThan[c1, c2: Card] {
    c1.rank < c2.rank
}

pred isSameColor[c1, c2: Card] {
    c1.color = c2.color
}

pred isSameSuit[c1, c2: Card] {
    c1.suit = c2.suit
}

pred allSameSuit {
    all disj c1, c2: Card | {
        c1.suit = c2.suit
    }
}

pred inEndPile[gs: GameState, ep: EndPile, c: Card] {
    c = gs.endPileTop[ep] or reachable[c, gs.endPileTop[ep], gs.cardBelow]
}


pred validEndPile[gs: GameState, ep: EndPile] {
    // every card in the end pile must match the pile's suit
    all c: Card | inEndPile[gs, ep, c] implies {
        c.suit = ep.endPileSuit
    }

    // cards in asc. order
    all c: Card | inEndPile[gs, ep, c] implies {
        some gs.cardBelow[c] implies {
            gs.cardBelow[c].rank = c.rank - 1
        }
    }

    // bottom card must be rank 1
    some gs.endPileTop[ep] implies {
        some bottom: Card | {
            inEndPile[gs, ep, bottom]
            no gs.cardBelow[bottom]
            bottom.rank = 1
        }
    }

}

pred completedEndPile[gs: GameState, ep: EndPile] {
    some gs.endPileTop[ep]
    gs.endPileTop[ep].rank = 3 
    validEndPile[gs, ep]
}


/*
Player movement predicates
*/

pred validMove {

}

/*
Game properties predicates
*/

pred gameComplete[gs: GameState] {
    all ep: EndPile | completedEndPile[gs, ep]
    all p: Pile | gs.pileEmpty[p] = True
    all d: Deck | gs.deckEmpty[d] = True
}

pred winnable {}
pred stayWinning {} //?

valid_ep: run {
    twelve_wellformed
    some gs: GameState | all ep: EndPile | validEndPile[gs, ep]
} for exactly 1 GameState, exactly 12 Card, 4 EndPile

game_complete: run {
    twelve_wellformed
    some gs: GameState | gameComplete[gs]
} for exactly 1 GameState, exactly 12 Card, 3 Pile, 4 EndPile, 1 Deck

// run {
//     wellformed
// } for exactly 1 GameState, 8 Card

// run {
//     some pile: Pile | pile.empty = False
//     legalPile
// } for exactly 1 Pile, 8 Card