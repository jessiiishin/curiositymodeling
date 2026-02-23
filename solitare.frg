#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}
abstract sig Suit {}
abstract sig Color {}
one sig Red, Black extends Color {}
one sig Heart, Diamond, Spade, Clover extends Suit {}

sig GameState {
    init: lone GameState,
    deckTop: lone Card,
    discardTop: lone Card,
    columnTop: pfunc Pile -> Card
}

sig Card {
    suit: one Suit,
    color: one Color,
    rank: one Int,
    faceDown: one Boolean,
    next: lone Card,
    prev: lone Card
}

sig Pile {
    stack: lone Card,
    empty: one Boolean
}

sig EndPile {
    endStack: lone Card,
    complete: one Boolean
}


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

pred wellformed {

}

pred wellformed_initial[gs: GameState] {
    #{p: Pile | p.empty = False} = 7
    some p1: Pile | #{reachable[p1, p1.stack, next]} = 1
    some gs.init
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

pred pileIsAscendingOrder { // A -> K
    all c: Card | {
        some c.next implies isLowerRankThan[c, c.next]
        some c.prev implies isLowerRankThan[c.prev, c]
    }
}

pred allSameSuit {
    all disj c1, c2: Card | {
        c1.suit = c2.suit
    }
}

// maybe we just need a legalPile pred and force forge to keep this pred
// true with every movement instead

pred legalPile {
    all pile: Pile | {
        all c: Card | {
            reachable[c, pile.stack, next]
            some c.next implies isLowerRankThan[c, c.next]
            some c.prev implies isLowerRankThan[c.prev, c]
        }
        one lastCard: Card | {
            lastCard.faceDown = False
            no lastCard.next
        }
    }
}

pred legalEndPile {
    all endpile: EndPile | {
        allSameSuit
        all c: Card | {
            reachable[c, endpile.stack, next]
            some c.next implies isLowerRankThan[c.next, c]
            some c.prev implies isLowerRankThan[c, c.prev]
            c.faceDown = True
        }
    }
}

pred pileIsDescendingOrder { // K -> A
    all c: Card | {
        some c.next implies isLowerRankThan[c.next, c]
        some c.prev implies isLowerRankThan[c, c.prev]
    }
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

run {
    wellformed
} for exactly 1 GameState, 8 Card