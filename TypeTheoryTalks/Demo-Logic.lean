/-!
The *Curry-Howard correspondence* treats propositions as types, proofs as terms, and
logical connectives and their rules as special cases of general constructions of types.

This file contains some logic puzzles in Lean.
-/

variable (P Q R : Prop)

example : P → P := sorry

example : P → (P → Q) := sorry
 
example : Q → (P → Q) := sorry

example : P ∧ Q → P := sorry

example : P ∧ Q → Q := sorry

example : P → Q → (P ∧ Q) := sorry

example : P → P ∨ Q := sorry

example : Q → P ∨ Q := sorry

example : (P → R) → (Q → R) → (P ∨ Q → R) := sorry

example : True := sorry

example : P → True := sorry

example : False → P := sorry

example : (True → False) → False := sorry

example : (P → False) → ¬P := sorry

example : (P → Q) → (¬Q → ¬P) := sorry