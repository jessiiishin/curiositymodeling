#lang forge/froglet


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
    nextCard: pfunc Card -> Card,
    prevCard: pfunc Card -> Card,

    endPileComplete: pfunc EndPile -> Boolean,
    pileEmpty: pfunc Pile -> Boolean
}
// if gamestate is what changes cards next and prev will not change

sig Card {
    suit: one Suit,
    color: one Color,
    rank: one Int
}

sig Pile {}
sig EndPile {}
sig Deck {}


/*
12 cards:
- 1, 2, 3 in each suit
- four suits

-> 3 piles with 1, 2, 3 cards, 6 cards in deck
*/
pred twelve_wellformed {
    // each suit has same number of cards
    all disj s1, s2: Suit | {
        #{c: Card | c.suit = s1} = #{c: Card | c.suit = s2}
    }

    // card ranking is limited to 1 to 3
    all c: Card | c.rank >= 1 and c.rank <= 3
    all disj c1, c2: Card | not (c1.suit = c2.suit and c1.rank = c2.rank)

    all c: Card | {
        (c.suit = Heart or c.suit = Diamond) iff (c.color = Red)
        (c.suit = Spade or c.suit = Clover) iff (c.color = Black)
    }
}

run {
    twelve_wellformed 
} for exactly 12 Card, 0 GameState

// pred wellformed_initial[gs: GameState] {
//     some state: GameState | {
//         all p: Pile | {
        
//         }
//     }
// }

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

pred completeEndPile { // for all rank ... 
    
}

/*
Player movement predicates
*/

pred validMove {}

/*
Game properties predicates
*/

pred winnable {}
pred stayWinning {} //?

// run {
//     wellformed
// } for exactly 1 GameState, 8 Card

// run {
//     some pile: Pile | pile.empty = False
//     legalPile
// } for exactly 1 Pile, 8 Card