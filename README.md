# curiositymodeling

Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

**Objective**

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
using a smaller game with only 12 cards total.

**Model Design and Visualization**

**Signatures and Predicates**

**Testing**

**Documentation**

Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?
Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.
Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.
Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.