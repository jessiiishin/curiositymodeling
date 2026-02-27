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
    (c = gs.deckTop) or (c in gs.deckTop.^(gs.cardBelow))
}

fun cardInDiscard[c: Card, gs: GameState, dis: Discard]: Boolean {
    (c = gs.discardTop) or (c in gs.discardTop.^(gs.cardBelow))
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


    all gs: GameState | {
        // linearity of stack
        all c1: Card {
            not gs.cardBelow[c1] = c1
            not reachable[c1, c1, gs.cardBelow]
        }

        // all end piles valid
        all ep: EndPile | validEndPile[gs, ep]

        // all piles valid
        all p: Pile | validPile[gs, p]

        // deck face down
        all c: Card | (inDeck[gs, c]) implies {
            gs.faceDown[c] = True
        }

        // discard face up
        all c: Card | (inDiscard[gs, c]) implies {
            gs.faceDown[c] = False
        }

        // prevent dags
        all disj c1, c2: Card | {
            some gs.cardBelow[c1] and some gs.cardBelow[c2] implies {
                gs.cardBelow[c1] != gs.cardBelow[c2]
            }
        }

        // face down properties when in deck or in discard
        all c: Card | inDeck[gs, c] implies gs.faceDown[c] = True
        all c: Card | inDiscard[gs, c] implies gs.faceDown[c] = False

        exclusiveDecksAndPiles[gs]
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

    // no two endpiles share the same top card
    all disj ep1, ep2: EndPile | all c: Card | {
        inEndPile[st, ep1, c] implies not inEndPile[st, ep2, c]
    }

    // no two piles share the same top card
    all disj p1, p2: Pile | all c: Card | {
        inPile[st, p1, c] implies not inPile[st, p2, c]
    }
}

pred validPile[gs: GameState, p: Pile] {
    // topmost card on pile should be face up
    some gs.columnTop[p] implies gs.faceDown[gs.columnTop[p]] = False

    // alternate colors
    all c: Card | (inPile[gs, p, c] and 
        some gs.cardBelow[c] and 
        inPile[gs, p, gs.cardBelow[c]] and 
        gs.faceDown[c] = False and 
        gs.faceDown[gs.cardBelow[c]] = False) implies {
        c.color != gs.cardBelow[c].color
    }

    // no face up card below a face down card
    all c: Card | {
        (inPile[gs, p, c] and some gs.cardBelow[c] and inPile[gs, p, gs.cardBelow[c]]) implies {
            gs.faceDown[c] = True implies gs.faceDown[gs.cardBelow[c]] = True
        }
    }

    // cards in pile are always in ascending order
    all c: Card | (inPile[gs, p, c] and gs.faceDown[c] = False and gs.faceDown[gs.cardBelow[c]] = False) implies {
        some gs.cardBelow[c] implies gs.cardBelow[c].rank = add[c.rank, 1]
    }
}

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

    // deck should not be empty
    some gs.deckTop

    // no discard pile
    no gs.discardTop

    // endpiles are empty & not complete
    all endPile: EndPile | { 
        no gs.endPileTop[endPile]
    }
}

pred twelve_init[gs: GameState] {
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

pred completedEndPile[gs: GameState, ep: EndPile] {
    some gs.endPileTop[ep]
    gs.endPileTop[ep].rank = 3 
    validEndPile[gs, ep]
}


/*
Player movement predicates
*/

/** GUARDS */
pred moveToPileGeneralGuard[targetCard, destCard: Card, destP: Pile, pre: GameState] {
    -- GUARD
    // targetCard must be different from destCard
    targetCard != destCard

    // both are face up
    pre.faceDown[targetCard] = False
    pre.faceDown[destCard] = False

    // targetCard must be lower in rank than destCard
    targetCard.rank = subtract[destCard.rank, 1]

    // targetCard must be different color than destCard
    targetCard.color != destCard.color

    // destCard must be the top card in one of a Pile
    pre.columnTop[destP] = destCard
}

pred movePileToPileGeneralFrame[targetCard: Card, srcP, destP: Pile, pre, post: GameState] {
    -- FRAME CONDITION
    // deck, endpiles, other piles, and discard stay same
    all ep: EndPile | pre.endPileTop[ep] = post.endPileTop[ep]
    all p: Pile | (p != srcP and p != destP) implies pre.columnTop[p] = post.columnTop[p]
    pre.deckTop = post.deckTop
    pre.discardTop = post.discardTop

    // all other cards remain in same facedown condition
    all c: Card | c != pre.cardBelow[targetCard] implies pre.faceDown[c] = post.faceDown[c]

    // all other cards remain in same order
    all c: Card | c != targetCard implies pre.cardBelow[c] = post.cardBelow[c]
}

/** ACTIONS */
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

pred resetDeck[pre, post: GameState] {
    -- GUARd
    no pre.deckTop
    some pre.discardTop

    -- ACTION
    // move bottom card to the top
    some bottom: Card | {
        inDiscard[pre, bottom]
        no pre.cardBelow[bottom]
        post.deckTop = bottom
    }

    // reverse every card
    all disj c1, c2: Card | (pre.cardBelow[c1] = c2 and inDiscard[pre, c1]) implies {
        post.cardBelow[c2] = c1
    }

    // last card in post has nothing
    no post.cardBelow[pre.discardTop]

    // all cards in post are now face down
    all c: Card | inDiscard[pre, c] implies {
        post.faceDown[c] = True
    }

    no post.discardTop

    -- FRAME
    all ep: EndPile | post.endPileTop[ep] = pre.endPileTop[ep]
    all p: Pile | post.columnTop[p] = pre.columnTop[p]
    
    all c: Card | not inDiscard[pre, c] implies {
        post.cardBelow[c] = pre.cardBelow[c]
        post.faceDown[c] = pre.faceDown[c]
    }

}

// SITUATION WHEN PILE IS EMPTY (only largest rank can move to empty pile)
// PILE -> END PILE
pred movePileToEmptyPile[targetCard: Card, srcP, destP: Pile, pre, post: GameState] {
    -- GUARD
    // empty destination pile
    no pre.columnTop[destP]
    
    // coming from another pile
    inPile[pre, srcP, targetCard]
    
    // face down
    pre.faceDown[targetCard] = False

    // all face up
    all c: Card | (inPile[pre, srcP, c] and reachable[targetCard, c, pre.cardBelow]) implies {
        pre.faceDown[c] = False
    }

    // then targetCard need to be the maximum rank
    all c: Card | c != targetCard implies {
        targetCard.rank >= c.rank
    }

    -- ACTION
    // card below targetCard it needs to be face up & become top card
    some pre.cardBelow[targetCard] implies {
        post.faceDown[pre.cardBelow[targetCard]] = False
        post.columnTop[srcP] = pre.cardBelow[targetCard]
    }
    
    // empty pile
    no pre.cardBelow[targetCard] implies {
        no post.columnTop[srcP]
    }

    // move card
    post.columnTop[destP] = pre.columnTop[srcP]
    no post.cardBelow[targetCard]

    -- FRAME CONDITION
    movePileToPileGeneralFrame[targetCard, srcP, destP, pre, post]
}

// PILE -> PILE
pred movePileToPile[targetCard, destCard: Card, srcP, destP: Pile, pre, post: GameState] {
    -- GUARD
    moveToPileGeneralGuard[targetCard, destCard, destP, pre]

    // targetCard is in the pile somewhere
    inPile[pre, srcP, targetCard]

    // source pile and destination pile is different
    srcP != destP

    // everything above targetCard in src pile is also face up
    all c: Card | (inPile[pre, srcP, c] and reachable[targetCard, c, pre.cardBelow]) implies {
        pre.faceDown[c] = False
    }

    -- ACTION
    // card below targetCard it needs to be face up & become top card
    some pre.cardBelow[targetCard] implies {
        post.faceDown[pre.cardBelow[targetCard]] = False
        post.columnTop[srcP] = pre.cardBelow[targetCard]
    }

    // empty pile
    no pre.cardBelow[targetCard] implies {
        no post.columnTop[srcP]
    }

    // move card
    post.cardBelow[targetCard] = destCard
    post.columnTop[destP] = pre.columnTop[srcP]
    

    -- FRAME CONDITION
    movePileToPileGeneralFrame[targetCard, srcP, destP, pre, post]
}

// END PILE -> PILE
pred moveEndPileToPile[targetCard, destCard: Card, srcEndP: EndPile, destP: Pile, pre, post: GameState] {
    -- GUARD
    moveToPileGeneralGuard[targetCard, destCard, destP, pre]

    // targetCard must be on top of source EndPile
    some pre.endPileTop[srcEndP] and pre.endPileTop[srcEndP] = targetCard

    -- ACTION
    // move card
    post.cardBelow[targetCard] = destCard
    post.columnTop[destP] = targetCard
    
    // card below targetCard in endpile becomes new top of endpile
    some pre.cardBelow[targetCard] implies {
        post.endPileTop[srcEndP] = pre.cardBelow[targetCard]
    }
    no pre.cardBelow[targetCard] implies {
        no post.endPileTop[srcEndP]
    }

    -- FRAME CONDITION
    // deck and discard the same
    post.deckTop = pre.deckTop
    post.discardTop = pre.discardTop

    // everything else is the same
    all ep: EndPile | ep != srcEndP implies post.endPileTop[ep] = pre.endPileTop[ep]
    all p: Pile | p != destP implies post.columnTop[p] = pre.columnTop[p]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | post.faceDown[c] = pre.faceDown[c]
}

// PILE -> END PILE
pred movePileToEndPile[targetCard: Card, srcP: Pile, destEP: EndPile, pre, post: GameState] {
    -- GUARD
    // moved card must be the top of an pile
    pre.columnTop[srcP] = targetCard
    pre.faceDown[targetCard] = False

    // targetCard suit = destCard suit
    targetCard.suit = destEP.endPileSuit

    // targetCard rank > destCard rank
    some pre.endPileTop[destEP] implies {
        targetCard.rank = add[pre.endPileTop[destEP].rank, 1]
    }
    
    // the first end card
    no pre.endPileTop[destEP] implies {
        targetCard.rank = 1
    }

    -- ACTION
    // targetCard cardBelow = destCard
    // post.endPile[endpile] = targetCard
    post.endPileTop[destEP] = targetCard
    post.cardBelow[targetCard] = pre.endPileTop[destEP]

    // card below becomes new top card
    some pre.cardBelow[targetCard] implies {
        post.columnTop[srcP] = pre.cardBelow[targetCard]
        post.faceDown[pre.cardBelow[targetCard]] = False
    }

    no pre.cardBelow[targetCard] implies {
        no post.columnTop[srcP]
    }

    -- FRAME CONDITION
    post.deckTop = pre.deckTop
    post.discardTop = pre.discardTop
    all ep: EndPile | ep != destEP implies post.endPileTop[ep] = pre.endPileTop[ep]
    all p: Pile | p != srcP implies post.columnTop[p] = pre.columnTop[p]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | c != pre.cardBelow[targetCard] implies post.faceDown[c] = pre.faceDown[c]
}

// DISCARD -> PILE
pred moveDiscardToEndPile[targetCard: Card, destEP: EndPile, pre, post: GameState] {
    -- GUARD
    pre.discardTop = targetCard
    pre.faceDown[targetCard] = False

    // suit match
    targetCard.suit = destEP.endPileSuit

    // if end pile is empty, targetCard must be rank 1 otherwise +1
    some pre.endPileTop[destEP] implies {
        targetCard.rank = add[pre.endPileTop[destEP].rank, 1]
    }

    no pre.endPileTop[destEP] implies {
        targetCard.rank = 1
    }

    -- ACTION
    post.endPileTop[destEP] = targetCard
    post.cardBelow[targetCard] = pre.endPileTop[destEP]

    some pre.cardBelow[targetCard] implies {
        post.discardTop = pre.cardBelow[targetCard]
    }
    no pre.cardBelow[targetCard] implies {
        no post.discardTop
    }

    -- FRAME CONDITION
    post.deckTop = pre.deckTop
    all p: Pile | post.columnTop[p] = pre.columnTop[p]
    all ep: EndPile | ep != destEP implies post.endPileTop[ep] = pre.endPileTop[ep]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | post.faceDown[c] = pre.faceDown[c]
}

pred moveDiscardToPile[targetCard: Card, destP: Pile, pre, post: GameState] {
    -- GUARD
    // top of discard
    pre.discardTop = targetCard
    pre.faceDown[targetCard] = False

    // move into a faceup column
    some pre.columnTop[destP]
    pre.faceDown[pre.columnTop[destP]] = False

    // exactly +1 
    targetCard.rank = subtract[pre.columnTop[destP].rank, 1]

    // diff color
    targetCard.color != pre.columnTop[destP].color

    -- ACTION
    // new top of pile
    post.columnTop[destP] = targetCard
    post.cardBelow[targetCard] = pre.columnTop[destP]

    // new top card in discard
    some pre.cardBelow[targetCard] implies {
        post.discardTop = pre.cardBelow[targetCard]
    }
    no pre.cardBelow[targetCard] implies {
        no post.discardTop
    }

    post.deckTop = pre.deckTop
    all p: Pile | p != destP implies post.columnTop[p] = pre.columnTop[p]
    all ep: EndPile | post.endPileTop[ep] = pre.endPileTop[ep]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | post.faceDown[c] = pre.faceDown[c]
}

pred moveDiscardToEmptyPile[targetCard: Card, destP: Pile, pre, post: GameState] {
    -- GUARD
    // top of discard
    pre.discardTop = targetCard
    pre.faceDown[targetCard] = False

    // pile is empty
    no pre.columnTop[destP]

    // target card is max
    all c: Card | c != targetCard implies {
        targetCard.rank >= c.rank
    }

    -- ACTION
    // new top of dest pile
    post.columnTop[destP] = targetCard
    no post.cardBelow[targetCard]

    // new top of discard
    some pre.cardBelow[targetCard] implies {
        post.discardTop = pre.cardBelow[targetCard]
    }
    no pre.cardBelow[targetCard] implies {
        no post.discardTop
    }

    -- FRAME
    post.deckTop = pre.deckTop
    all p: Pile | p != destP implies post.columnTop[p] = pre.columnTop[p]
    all ep: EndPile | post.endPileTop[ep] = pre.endPileTop[ep]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | post.faceDown[c] = pre.faceDown[c]
}

pred moveEndPileToEmptyPile[targetCard: Card, srcEP: EndPile, destP: Pile, pre, post: GameState] {
    -- GUARD
    // target card top of ep
    pre.endPileTop[srcEP] = targetCard
    pre.faceDown[targetCard] = False

    // destination is empty
    no pre.columnTop[destP]

    // target card is max
    all c: Card | c != targetCard implies {
        targetCard.rank >= c.rank
    }

    -- ACTION
    // top of dest pile
    post.columnTop[destP] = targetCard
    no post.cardBelow[targetCard]

    // new end pile top
    some pre.cardBelow[targetCard] implies {
        post.endPileTop[srcEP] = pre.cardBelow[targetCard]
    }
    no pre.cardBelow[targetCard] implies {
        no post.endPileTop[srcEP]
    }

    -- FRAME
    post.deckTop = pre.deckTop
    post.discardTop = pre.discardTop
    all p: Pile | p != destP implies post.columnTop[p] = pre.columnTop[p]
    all ep: EndPile | ep != srcEP implies post.endPileTop[ep] = pre.endPileTop[ep]
    all c: Card | c != targetCard implies post.cardBelow[c] = pre.cardBelow[c]
    all c: Card | post.faceDown[c] = pre.faceDown[c]

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
    all gs: GameState | gameComplete[gs] implies {
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
    some gs: GameState | {
        gameComplete[gs]
        reachable[gs, Solitaire.init, Solitaire.next]
    }
}


pred validMove[pre: GameState, post: GameState] {
    twelve_wellformed
    not gameComplete[pre]
    pre != post
    
    some c, c2: Card, p, p2: Pile, ep: EndPile | {
        drawCard[pre, post] or
        resetDeck[pre, post] or
        movePileToPile[c, c2, p, p2, pre, post] or
        movePileToEmptyPile[c, p, p2, pre, post] or
        movePileToEndPile[c, p, ep, pre, post] or
        moveEndPileToPile[c, c2, ep, p, pre, post] or
        moveEndPileToEmptyPile[c, ep, p, pre, post] or
        moveDiscardToPile[c, p, pre, post] or
        moveDiscardToEmptyPile[c, p, pre, post] or
        moveDiscardToEndPile[c, ep, pre, post]
    }
}

pred validGame {
    twelve_wellformed
    twelve_init[Solitaire.init] 

    all disj gs1, gs2: GameState | {
        some gs1.deckTop != gs2.deckTop or
        some gs1.discardTop != gs2.discardTop or
        (some p: Pile | gs1.columnTop[p] != gs2.columnTop[p]) or
        (some ep: EndPile | gs1.endPileTop[ep] != gs2.endPileTop[ep]) or
        (some c: Card | gs1.cardBelow[c] != gs2.cardBelow[c])
    }

    all gs: GameState | some Solitaire.next[gs] implies validMove[gs, Solitaire.next[gs]]
}

valid_and_winnable: run {
    validGame
    winnable
} 
for exactly 12 Card, exactly 3 Pile, exactly 4 EndPile, 20 GameState
for {next is linear}

one_ep_complete: run {
    validGame
    some gs: GameState | some ep: EndPile | completedEndPile[gs, ep]
} for exactly 12 Card, exactly 3 Pile, exactly 4 EndPile, 8 GameState
for {next is linear}


one_move_pile_to_pile: run {
    twelve_wellformed

    some disj pre, post: GameState | {
        not gameComplete[pre]
        some c1, c2: Card, p1, p2: Pile | {
            movePileToPile[c1, c2, p1, p2, pre, post]
        }
    }
} for exactly 12 Card, 2 GameState, exactly 3 Pile

init_move_pile_to_pile: run {
    twelve_wellformed
    
    some disj pre, post: GameState | {
        twelve_init[pre]
        not gameComplete[pre]
        some c1, c2: Card, p1, p2: Pile | {
            movePileToPile[c1, c2, p1, p2, pre, post]
        }
    }
}

twelve_cards: run {
    twelve_wellformed 
} for exactly 12 Card, 1 GameState, exactly 4 EndPile

twelve_cards_wellformed_deal: run {
    twelve_wellformed
    some gs: GameState | twelve_init[gs]
} for exactly 12 Card, exactly 1 GameState, exactly 3 Pile, exactly 4 EndPile, exactly 1 Deck


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

reset_deck: run {    
    twelve_wellformed
    some pre, post: GameState | resetDeck[pre, post]
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
