#lang forge


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
    
    faceDown: pfunc Card -> Boolean,
    cardBelow: pfunc Card -> Card,
    cardAbove: pfunc Card -> Card,

    endPileComplete: pfunc EndPile -> Boolean,
    pileEmpty: pfunc Pile -> Boolean,
    deckEmpty: pfunc Deck -> Boolean
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
        all disj c1, c2: Card | {
            reachable[c2, c1, st.cardBelow] implies {
                reachable[c1, c2, st.cardAbove]
                not reachable[c1, c2, st.cardBelow]
                not reachable[c2, c1, st.cardAbove]
            }
        }

        exclusiveDecksAndPiles[st]

        all p: Pile, ep: EndPile | {
            st.pileEmpty[p] = True iff st.columnTop[p] = none
        }
        // if a pile or endPile or deck is not empty, then it must have at least one card that it can reach

        // there is only one deck
        // one deck: Deck | #{cardInDeck: Card | reachable[cardInDeck]}
        // and if card is in deck it's not in any of the columns or end pile and etc.
    }

    
}

pred exclusiveDecksAndPiles[st: GameState] {
    all c: Card, p: Pile, ep: EndPile, d: Deck | {
        // always in some pile / deck / endpile
        (reachable[c, st.columnTop[p], st.cardBelow] or
        reachable[c, st.deckTop[d], st.cardBelow] or
        reachable[c, st.endPileTop[ep], st.cardBelow])

        // exclusive
        (reachable[c, st.columnTop[p], st.cardBelow] implies (
            not reachable[c, st.deckTop[d], st.cardBelow] and
            not reachable[c, st.endPileTop[ep], st.cardBelow]
        ))

        (reachable[c, st.deckTop[d], st.cardBelow] implies (
            not reachable[c, st.columnTop[p], st.cardBelow] and
            not reachable[c, st.endPileTop[ep], st.cardBelow]
        ))

        (reachable[c, st.endPileTop[ep], st.cardBelow] implies (
            not reachable[c, st.columnTop[p], st.cardBelow] and
            not reachable[c, st.deckTop[d], st.cardBelow]
        ))
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
        some gs.columnTop[p] implies gs.faceDown[gs.columnTop[p]] = False
    }

    // deck should not be empty and all cards are face down
    all d: Deck, c: Card | {
        gs.deckEmpty[d] = False
        (gs.deckTop[d] = c or reachable[c, gs.deckTop[d], gs.cardBelow]) implies {
            gs.faceDown[c] = True
        }
    }

    // endpiles are empty & not complete
    all endPile: EndPile | { 
        gs.endPileComplete[endPile] = False
        no c: Card | reachable[c, gs.endPileTop[endPile], gs.cardBelow]
    }
}

pred twelve_init {
    some gs: GameState | {
        // some disj p1, p2, p3: Pile | {
        //     some disj c1, c2, c3: Card | {
        //         gs.columnTop[p1] = c1
        //         gs.columnTop[p2] = c2
        //         gs.columnTop[p3] = c3
        //     }

        //     #{c: Card | reachable[c, gs.columnTop[p1], gs.cardBelow]} = 0
        //     #{c: Card | reachable[c, gs.columnTop[p2], gs.cardBelow]} = 1
        //     #{c: Card | reachable[c, gs.columnTop[p3], gs.cardBelow]} = 2
        // }

        some d: Deck | {
            some c: Card | gs.deckTop[d] = c 
            #{c: Card | reachable[c, gs.deckTop[d], gs.cardBelow]} = 5
        }
    }
}

run {
    twelve_wellformed 
} for exactly 12 Card, 0 GameState

run {
    twelve_wellformed
    twelve_init
    some st: GameState | wellformed_initial[st]
} for exactly 12 Card, 1 GameState, 3 Pile, 4 EndPile, 1 Deck



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

// pred legalPile {
//     all pile: Pile | {
//         all c: Card | reachable[c, pile.stack, next] implies {
//             some c.next implies isLowerRankThan[c, c.next]
//             some c.prev implies isLowerRankThan[c.prev, c]
//             c.faceDown = True
//         }
//         some pile.stack iff pile.empty = False
//         // last card is faceDown = False
//     }
// }

// pred legalEndPile {
//     all endpile: EndPile | {
//         allSameSuit
//         all c: Card | reachable[c, endpile.stack, next] {
//             some c.next implies isLowerRankThan[c.next, c]
//             some c.prev implies isLowerRankThan[c, c.prev]
//             c.faceDown = False
//         }
        
//     }
// }

pred completeEndPile[gs: GameState, ep: EndPile] { // for all rank ... 
    gs.endPileComplete[ep] in True iff {
        // some predicate to check end pile is complete
    }
}

/*
Player movement predicates
*/

pred validMove {}

/*
Game properties predicates
*/

pred win[gs: GameState] {
    all ep: EndPile | some gs.endPileComplete[ep] implies {
        gs.endPileComplete[ep] in True
    }

    all pile: Pile | some gs.pileEmpty[pile] implies {
        gs.pileEmpty[pile] in True
    }
}

pred winnable {}
pred stayWinning {} //?

// run {
//     wellformed
// } for exactly 1 GameState, 8 Card

// run {
//     some pile: Pile | pile.empty = False
//     legalPile
// } for exactly 1 Pile, 8 Card