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

### Design Choices

Our model represents the game in snapshots through the `GameState` sig. Each `GameState` tracks the top card of the deck, discard pile, each tableau pile and end piles. It also has a `cardBelow` set that encodes the stack structure, and a `faceDown` set that tells us whether the card is face up or face down.

### Run Statements

We wrote roughly three different types of run statements:

- **Single-state sanity checks**: `twelve_cards`, `twelve_cards_wellformed_deal`, `valid_ep`, `game_complete` -- verifies that wellformed and initial/complete states exist at all.
- **Transitions:** `mv_drawCard`, `mv_resetDeck`, `mv_movePileToPile`, etc. -- each verifies that a specific move predicate can be satisfied between two game states.
- **Game traces:** `valid_and_winnable`, `valid_not_winnable`, `stuck` — full game traces that are winnable, unwinnable, or reach some stuck position.

### Visualization

As part of our model, we wrote a custom visualizer `layout.cnd`. However, it does not properly allow us to visualize multi-state games. It is recommended and useful only in single-state environments.

- We project onto the `GameState`
- `cardBelow` edges show the stacking and linear structure. Follow them downward to read a pile from top to bottom.
- `faceDown` edges show `True` or `False` for each card in each state.
- `columnTop`, `deckTop`, `discardTop`, and `endPileTop` edges show the entry points into each stack.

For multi-state traces, the projection onto `GameState` allows us to step through each `GameState` and observe the changes.

### Signatures

| Sig              | Purpose                                                                                              |
| ---------------- | ---------------------------------------------------------------------------------------------------- |
| `Card`           | A playing card with a fixed `suit`, `color`, and `rank`. Static across all game states.              |
| `Suit` / `Color` | Abstract types for the four suits and two colors.                                                    |
| `GameState`      | A snapshot of the game: pile tops, deck/discard tops, face-down status, and the below-card relation. |
| `Pile`           | A tableau column. Cards stack on top of each other following alternating-color, differ-by-one rules. |
| `EndPile`        | A foundation pile, one per suit, built upward from rank 1.                                           |
| `Solitaire`      | A singleton holding the initial `GameState` and the `next` transition function.                      |

### Predicates

#### Location Helpers

These help us determine where a given card is in the game.

| Predicate              | Description                                                                                                        |
| ---------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `inDeck[gs, c]`        | True if card `c` is in the deck in state `gs`: either it is `deckTop` or reachable from `deckTop` via `cardBelow`. |
| `inDiscard[gs, c]`     | True if card `c` is in the discard pile: either it is `discardTop` or reachable from it via `cardBelow`.           |
| `inPile[gs, p, c]`     | True if card `c` is in tableau pile `p`: either it is `columnTop[p]` or reachable from it via `cardBelow`.         |
| `inEndPile[gs, ep, c]` | True if card `c` is in end pile `ep`: either it is `endPileTop[ep]` or reachable from it via `cardBelow`.          |

#### Wellformedness

These specify the wellformedness of each state.

| Pred                     | Purpose                                                                                                                                                                                                |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `general_wellformed`     | Invariants holding across all game states: card uniqueness, color/suit consistency, stack linearity (no cycles), exclusivity (each card in exactly one location), and face-up/down rules per location. |
| `twelve_wellformed`      | Specializes to the 12-card variant by bounding ranks to 1–3.                                                                                                                                           |
| `validPile`              | A tableau pile must have its top card face-up, alternate colors in the face-up section, and have differ-by-one ranks among consecutive face-up cards.                                                  |
| `validEndPile`           | A foundation pile must contain only one suit, all face-up, in ascending rank from 1 at the bottom.                                                                                                     |
| `exclusiveDecksAndPiles` | Every card belongs to exactly one location, with no card appearing in two piles simultaneously.                                                                                                        |

#### Guard and Frame Helpers

| Pred                                                             | Purpose                                                                                                                                                                                                                                                                                                                                                                                                           |
| ---------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `moveToPileGeneralGuard[targetCard, destCard, destP, pre]`       | Shared guard for any move that places a card onto a non-empty tableau pile. Checks the two cards are distinct; both are face-up; `targetCard` has rank exactly one less than `destCard`; they are different colors; `destCard` is the current top of `destP`. Used by `movePileToPile` and `moveEndPileToPile`.                                                                                                   |
| `movePileToPileGeneralFrame[targetCard, srcP, destP, pre, post]` | Shared frame condition for tableau-to-tableau moves. Freezes all end pile tops, all tableau tops except `srcP` and `destP`, the deck top, and the discard top. Freezes all `cardBelow` relations except `targetCard`'s. Freezes all `faceDown` values except `pre.cardBelow[targetCard]` which allows the newly exposed card in `srcP` to be flipped face-up. Used by `movePileToPile` and `movePileToEmptyPile`. |

#### Move Predicates

Each move predicate has a guard, an action and a frame condition.

| Pred                                                                 | Action                                                                                          |
| -------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- |
| `drawCard[pre, post]`                                                | Flips the top deck card face-up and moves it onto the discard pile.                             |
| `resetDeck[pre, post]`                                               | Reverses the entire discard pile back into the deck.                                            |
| `movePileToPile[targetCard, destCard, srcP, destP, pre, post]`       | Moves a card or a stack of cards from one pile to pile.                                         |
| `movePileToEmptyPile[targetCard, srcP, destP, pre, post]`            | Moves a maximum-rank card to an empty pile.                                                     |
| `movePileToEndPile[targetCard, srcP, destEP, pre, post]`             | Moves a card from the pile to the end pile.                                                     |
| `moveEndPileToPile[targetCard, destCard, srcEndP, destP, pre, post]` | Moves a card from one of the end piles into a tableau pile.                                     |
| `moveEndPileToEmptyPile[targetCard, srcEP, destP, pre, post]`        | Moves a card from one of the end piles into an empty pile. Only possible with the maximum card. |
| `moveDiscardToPile[targetCard, destP, pre, post]`                    | Moves the top card from the discard pile to a tableau pile.                                     |
| `moveDiscardToEmptyPile[targetCard, destP, pre, post]`               | Moves the top discard card to an empty tableau pile.                                            |
| `moveDiscardToEndPile[targetCard, destEP, pre, post]`                | Moves the top discard card directly onto its matching end pile.                                 |

#### Game Predicates

| Pred                       | Purpose                                                                                                                                                  |
| -------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `completedEndPile[gs, ep]` | Check if an end pile is completed for a given state. Useful for when all end piles are completed.                                                        |
| `gameComplete[gs]`         | Check if the game has been won. True when all end piles are completed, and all the other piles are empty.                                                |
| `winnable`                 | Checks if some game is winnable based on the initial state.                                                                                              |
| `validMove[pre, post]`     | Checks for if a move from some `pre` state to `post` state is valid.                                                                                     |
| `validGame`                | The top-level game trace predicate. Requires wellformedness across all states, a wellformed initial state, and for all moves between traces to be valid. |

## Testing

## Documentation

The model file is organized into clearly labeled sections:

1. **Type definitions** — suits, colors, cards, piles
2. **Wellformedness predicates** — invariants that must hold in every game state
3. **Location predicates** — `inDeck`, `inDiscard`, `inPile`, `inEndPile`
4. **Move predicates** — one per legal action, each with guard/action/frame comments
5. **Game-level predicates** — `validMove`, `validGame`, `winnable`, `gameComplete`
6. **Run statements** — grouped by purpose (sanity checks, move tests, game traces)
