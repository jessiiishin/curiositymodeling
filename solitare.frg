#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Card {
    // suit: something,
    // rank: Int,
    // color: maybe?
    // faceDown: Boolean,
    nextCard: lone Card,
    prevCard: lone Card
}

sig Space { // where the cards are on the board? the playing space?
    stack: set Card // can we use set when we're modeling order??? also can we use set in froglet
    // empty: boolean?
}

sig EndSpace {
    endStack: set Card,
    // complete: boolean?
}

/*
Things to possibly implement

when are cards stackable?:
- alternating colors
- in order of rank, never out of order

when are cards stackable in the complete pile?:
- same suite
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

/*
Card stack properties related predicates
*/

pred isLowerRankThan[c1, c2: Card] {
    
}

pred isSameColor[c1, c2: Card] {
    
}

pred isSameSuit[c1, c2: Card] {
    
}

pred stackIsAscendingOrder {
    
}

pred stackIsDescendingOrder {
    
}

