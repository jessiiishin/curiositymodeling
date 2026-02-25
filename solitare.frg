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
    discardTop: pfunc EndPile -> Card,
    columnTop: pfunc Pile -> Card,
    
    faceDown: pfunc Card -> Boolean,
    // nextCard: pfunc Card -> Card,
    // prevCard: pfunc Card -> Card,

    endPileComplete: pfunc EndPile -> Boolean,
    pileEmpty: pfunc Pile -> Boolean,

    // define next and prev in gamestate
    nextCard: pfunc Card -> Card,
    prevCard: pfunc Card -> Card
}
// if gamestate is what changes cards next and prev will not change

sig Card {
    suit: one Suit,
    color: one Color,
    rank: one Int
    // next: lone Card,
    // prev: lone Card
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
            reachable[c2, c1, st.nextCard] implies {
                reachable[c1, c2, st.prevCard]
                not reachable[c1, c2, st.nextCard]
                not reachable[c2, c1, st.prevCard]
            }
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

twelve_wf: run {
    twelve_wellformed 
} for exactly 12 Card, 0 GameState

pred wellformed_initial[gs: GameState] {
    // all piles should be full
    all p: Pile | {
        gs.pileEmpty[p] = False
    }

    // endpiles are empty (not complete)
    all endPile: Pile | { 
        gs.endPileComplete[endPile] = False
    }

    // all c: Card | reachable[c, gs.nextCard]
    
    // all cards except for one (the one on the top) are facedown
    // pile has increasing number of cards
    // deck has rest of the cards not in pile
}

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

pred completedEndPile[gs: GameState, ep: EndPile] {
    // this top pile exists and has rank 3
    some gs.discardTop[ep]
    gs.discardTop[ep].rank = 3

    // all cards in end pile share a suit
    all c: Card | {
        reachable[c, gs.discardTop[ep], gs.prevCard]
    } implies c.suit = ep.endPileSuit

    // all cards ascends
    all c: Card | {
        some gs.nextCard[c] implies {
            gs.nextCard[c].rank = c.rank + 1
        }
    }

    // exactly 3 cards in the pile
    #{ c: Card | reachable[c, gs.discardTop[ep], gs.prevCard] } = 3
}


/*
Player movement predicates
*/

pred validMove {}

/*
Game properties predicates
*/

pred gameComplete[gs: GameState] {
    all ep: EndPile | completedEndPile[gs, ep]

    all pile: Pile | some gs.pileEmpty[pile] implies {
        gs.pileEmpty[pile] = True
    }
}

pred winnable {}
pred stayWinning {} //?

complete: run {
    twelve_wellformed
    some gs: GameState | gameComplete[gs]
    // some gs: GameState | {
    //     all disj c1, c2: Card | {
    //         gs.nextCard[c1] = c2 iff c2.prev = c1
    //         gs.nextCard[c1] = c2 iff c1.next = c2
    //     }
    // }
} for exactly 1 GameState, 12 Card

// run {
//     wellformed
// } for exactly 1 GameState, 8 Card

// run {
//     some pile: Pile | pile.empty = False
//     legalPile
// } for exactly 1 Pile, 8 Card