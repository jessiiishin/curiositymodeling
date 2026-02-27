# 🃏 Solitaire

### <center>♠️  ♥️  ♣️  ♦️</center>

---

## Project Objective

The objective of this model is to model Klondike (solitaire). Klondike is a type of solitaire game
where the goal is to sort a standard deck of cards (52 cards, 4 suits, excluding Jokers) into their
respective suits in ascending order. You start with a tableau of seven fanned piles, each pile
from left to right has respectively 1 card, 2 cards, 3 cards, etc. The top most card of the piles
are facing up, all the others are facing down. All the other cards are put into a deck. In each
move, you may either draw from the deck or move cards around in the tableau or move cards into
the foundations (goal).

The cards in the tableau must be placed in a specific pattern, you can place cards on top of each
other only if they are alternating colors and maintaining a sequential, descending order. If there
are no moves you can make, you lose the game.

We explored if there are specific deals of the cards that makes the game inherently unbeatable,
how to model a game that's winnable, using a smaller game with only 12 cards total.

## Model Design and Visualization

### Signatures and Predicates

#### Signatures

- Boolean (True, False):
    - Abstract sig extended by True and False.
    - Represents rudimentary boolean logic.

- Suit (Heart, Diamond, Spade, Clover):
    - Abstract sig extended by Heart, Diamond, Spade, Clover.
    - Represents the four suits of a standard 52 card deck.

- Color (Red, Black):
    - Abstract sig extended by Red, Black.
    - Represents the two colors that a given card can be.

- Solitaire
- GameState
- Card
- Pile
- EndPile
- Deck
- Discard

#### Predicates

- general_wellformed:
    - Enforces that the deals (whatever the number of cards are) are wellformed.
    - Cards have a suits and colors that correspond to each other, no duplicate cards, the number
      of foundations = number of suits, a stack of cards is linear, and cards cannot appear in
      multiple stacks (deck, pile, endpile, etc.) at once.

- twelve_wellformed:
    - Enforces that there are twelve wellformed cards, ranks from 1 to 3.

- wellformed_initial:
    - Defines what a good starting state is like.
    - Tableau cards in piles should all be facing down except for the topmost one, EndPiles should
      be empty, piles should not be empty, deck should not be empty, discard should be empty

- twelve_init:
    - Defines what a good starting state is like for specifically twelve cards.
    - 3 piles, first one has 1 card, second one has 2 cards, third has 3. Deck has 6 cards.

- validEndPile:
    - Defines what a valid EndPile (foundation) should be.
    - Every card should match the EndPile's suit, be in descending order (K->A top to bottom),
      bottom card rank = 1, all cards face up.

- completedEndPile:
    - Defines what a complete EndPile (foundation) should be for twelve cards.
    - It's a valid EndPile with Topmost card's rank being 3.

- validMove:
    - Defines what a valid move is. Player can take one of the following moves:
        - moveToPile

- moveToPileGeneralGuard:
- movePileToPileGeneralFrame
- movePileToEmptyPile:
- movePileToPile:
- moveEndPileToPile:

- drawCard
- moveCardToFoundation
- gameComplete
- stayComplete
- winnable

### Testing

**Documentation**

Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.
Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.
