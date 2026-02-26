#lang forge

option run_sterling "layout.cnd"

abstract sig Boolean {}
one sig True, False extends Boolean {}
abstract sig Suit {}
abstract sig Color {}
one sig Red, Black extends Color {}
one sig Heart, Diamond, Spade, Clover extends Suit {}

one sig Solitaire {
    init: one GameState,
    next: pfunc GameState -> GameState
}

sig GameState {
    deckTop: lone Card,
    discardTop: lone Card,
    endPileTop: pfunc EndPile -> Card,
    columnTop: pfunc Pile -> Card, // top of stack
    
    faceDown: func Card -> Boolean,
    cardBelow: pfunc Card -> Card
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
one sig Deck {}
one sig Discard {}

/*
Helper functions to check card is part of pile, endpile, deck, or discard
*/
fun cardInPile[c: Card, gs: GameState, p: Pile]: Boolean {
    (c = gs.columnTop[p]) or (c in gs.columnTop[p].^(gs.cardBelow))
}

fun cardInEndPile[c: Card, gs: GameState, ep: EndPile]: Boolean {
    (c = gs.endPileTop[ep]) or (c in gs.endPileTop[ep].^(gs.cardBelow))
}

fun cardInDeck[c: Card, gs: GameState, d: Deck]: Boolean {
    (c = gs.deckTop[d]) or (c in gs.deckTop[d].^(gs.cardBelow))
}

fun cardInDiscard[c: Card, gs: GameState, dis: Discard]: Boolean {
    (c = gs.discardTop[dis]) or (c in gs.discardTop[dis].^(gs.cardBelow))
}


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

    // no 2 cards are the same
    all disj c1, c2: Card | not (c1.suit = c2.suit and c1.rank = c2.rank)

    // # of endpile = # of suits
    all s: Suit | {
        one endPile: EndPile | endPile.endPileSuit = s
    }

    // linearity of stack
    all st: GameState | {
        all c1: Card {
            not st.cardBelow[c1] = c1
            not reachable[c1, c1, st.cardBelow]
        }

        // no face up card below a face down card
        all p: Pile | {
            all c: Card | {
                (inPile[st, p, c] and some st.cardBelow[c] and inPile[st, p, st.cardBelow[c]]) implies {
                    st.faceDown[c] = True implies st.faceDown[st.cardBelow[c]] = True
                }
            }
        }

        // prevent dags
        all disj c1, c2: Card | {
            some st.cardBelow[c1] and some st.cardBelow[c2] implies {
                st.cardBelow[c1] != st.cardBelow[c2]
            }
        }

        exclusiveDecksAndPiles[st]
    }

    // all disj gs1, gs2: GameState | Solitaire.next[gs1] = gs2 implies {
    //     validMove[gs1, gs2]
    // }
}

pred inDiscard[gs: GameState, c: Card] {
    c = gs.discardTop or reachable[c, gs.discardTop, gs.cardBelow]
}

pred inPile[gs: GameState, p: Pile, c: Card] {
    c = gs.columnTop[p] or reachable[c, gs.columnTop[p], gs.cardBelow]
}

pred inEndPile[gs: GameState, ep: EndPile, c: Card] {
    c = gs.endPileTop[ep] or reachable[c, gs.endPileTop[ep], gs.cardBelow]
}

pred inDeck[gs: GameState, c: Card] { 
    c = gs.deckTop or reachable[c, gs.deckTop, gs.cardBelow]
}

pred exclusiveDecksAndPiles[st: GameState] {
    all c: Card | {
        let someInPile = (some p: Pile | inPile[st, p, c]) |
        let someInEndPile = (some ep: EndPile | inEndPile[st, ep, c]) |
        let someInDeck = (inDeck[st, c]) |
        let someInDiscard = inDiscard[st, c] | {
            someInPile or someInEndPile or someInDeck or someInDiscard

            (someInPile implies not someInEndPile and not someInDeck and not someInDiscard)
            (someInEndPile implies not someInPile and not someInDeck and not someInDiscard)
            (someInDeck implies not someInPile and not someInEndPile and not someInDiscard)
            (someInDiscard implies not someInPile and not someInEndPile and not someInDeck)
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
}

pred wellformed_initial[gs: GameState] {
    // all piles should be full
    // top of stack has face up, everything else has face down
    all p: Pile | {
        some gs.columnTop[p]
        gs.faceDown[gs.columnTop[p]] = False

        all c: Card | {
            (reachable[c, gs.columnTop[p], gs.cardBelow] and c != gs.columnTop[p]) implies {
                gs.faceDown[c] = True
            }
        }
    }

    // deck should not be empty and all cards are face down
    some gs.deckTop
    all c: Card | (inDeck[gs, c]) implies {
        gs.faceDown[c] = True
    }

    // no discard pile
    no gs.discardTop

    // endpiles are empty & not complete
    all endPile: EndPile | { 
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

        #{c: Card | reachable[c, gs.deckTop, gs.cardBelow]} = 5

        wellformed_initial[gs]
    }
}

twelve_cards: run {
    twelve_wellformed 
} for exactly 12 Card, 1 GameState, exactly 4 EndPile

twelve_cards_wellformed_deal: run {
    twelve_wellformed
    twelve_init
} for exactly 12 Card, exactly 1 GameState, exactly 3 Pile, exactly 4 EndPile, exactly 1 Deck


pred validEndPile[gs: GameState, ep: EndPile] {
    // every card in the end pile must match the pile's suit
    all c: Card | inEndPile[gs, ep, c] implies {
        c.suit = ep.endPileSuit
    }

    // for sake of argument, let them all be faceup
    all c: Card | inEndPile[gs, ep, c] implies {
        gs.faceDown[c] = False
    }

    // cards in desc. order
    all c: Card | inEndPile[gs, ep, c] implies {
        some gs.cardBelow[c] implies {
            gs.cardBelow[c].rank = subtract[c.rank, 1]
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

pred validMove[pre: GameState, post: GameState] {
    -- GUARD
    // wellformed
    // not winning, game is not finished
    not gameComplete[pre]
    
    -- ACTION
    moveTableauCard[pre, post] or
    drawCard[pre, post] or 
    moveCardToFoundation[pre, post]

    -- FRAME CONDITION
}

pred moveToPile[destP: Pile, pre, post: GameState] {
    -- GUARD
    // targetCard must be different from destCard
    some disj targetCard, destCard: Card | {
        // both are face up
        pre.faceDown[targetCard] = False
        pre.faceDown[destCard] = False

        // targetCard is either top of an EndPile or on top of Deck/Discard or on top of a pile or top of pile 
        ((some p: Pile | pre.columnTop[p] = targetCard and p != destP) or
        (some ep: EndPile | pre.endPileTop[ep] = targetCard) or
        (some dis: Discard | pre.discardTop[ep] = targetCard))

        // targetCard must be lower in rank than destCard
        targetCard.rank < destCard.rank

        // targetCard must be different color than destCard
        targetCard.color != destCard.color

        // destCard must be the top card in one of a Pile
        pre.columnTop[destP] = destCard

        -- ACTION
        post.cardBelow[targetCard] = destCard
        post.columnTop[destP] = targetCard
    }

    -- FRAME CONDITION
    all c: Card
    // deck stays same
    // end piles stay same
    // other piles stay same
    // other cards in destination cards don't change orders
}

pred drawCard[pre, post: GameState] {
    -- GUARD
    // there must be at least one card in the deck
    some pre.deckTop
    
    -- ACTION
    // previous top of deck becomes top of discard
    pre.deckTop = post.discardTop

    // previous top of discard goes below new top of discord
    post.cardBelow[post.discardTop] = pre.discardTop
    post.deckTop = pre.cardBelow[pre.deckTop]

    // top of deck -> faceDown = False
    // move to discard
    post.faceDown[post.discardTop] = False

    -- FRAME CONDITION
    // piles consistent
    all ep: EndPile | post.endPileTop[ep] = pre.endPileTop[ep]
    all p: Pile | post.columnTop[p] = pre.columnTop[p]

    // face down still same and card below same
    all c: Card | c != post.discardTop implies {
        post.cardBelow[c] = pre.cardBelow[c]
        post.faceDown[c] = pre.faceDown[c]
    }
}

pred moveCardToFoundation[pre, post: GameState] {
    -- GUARD
    // targetCard must be a card from a Pile or Discard
    // destCard must be the top of an EndPile
    // targetCard rank > destCard rank
    // targetCard suit = destCard suit
    // (correspondingly) targetCard color = destCard color idk if this needs to be extra enforced

    -- ACTION
    // targetCard cardBelow = destCard
    // post.endPile[endpile] = targetCard

    -- FRAME CONDITION
}

/*
Game properties predicates
*/

pred gameComplete[gs: GameState] {
    all ep: EndPile | completedEndPile[gs, ep]
    all p: Pile | no gs.columnTop[p]
    no gs.deckTop
    no gs.discardTop
}

pred stayComplete {
    some gs: GameState | gameComplete[gs] implies {
        all post: GameState | reachable[post, gs, next] implies {
            all ep: EndPile | gs.endPileTop[ep] = post.endPileTop[ep]
            all p: Pile | gs.columnTop[p] = post.columnTop[p]
            
            all c: Card | {
                gs.cardBelow[c] = post.cardBelow[c]
                gs.faceDown[c] = post.faceDown[c]
            }
            no post.deckTop
            no post.discardTop
        }
    }
} //?

pred winnable {
    some gs: GameState | gameComplete[gs] implies {
        reachable[gs, init, next]
    }
}

valid_ep: run {
    twelve_wellformed
    some gs: GameState | all ep: EndPile | validEndPile[gs, ep]
} for exactly 12 Card, exactly 1 GameState, exactly 3 Pile, exactly 4 EndPile

game_complete: run {
    twelve_wellformed
    some gs: GameState | gameComplete[gs]
} for exactly 1 GameState, exactly 12 Card, exactly 3 Pile, exactly 4 EndPile

draw_card: run {    
    twelve_wellformed
    some pre, post: GameState | drawCard[pre, post]
} 
for exactly 2 GameState, exactly 12 Card, exactly 3 Pile, exactly 4 EndPile
for {next is linear}

// run {
//     wellformed
// } for exactly 1 GameState, 8 Card

// run {
//     some pile: Pile | pile.empty = False
//     legalPile
// } for exactly 1 Pile, 8 Card
