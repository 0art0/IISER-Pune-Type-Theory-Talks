/-!
The *Curry-Howard correspondence* treats propositions as types, proofs as terms, and
logical connectives and their rules as special cases of general constructions of types.

This file contains some logic puzzles in Lean.
-/

variable (P Q R : Prop)

example : P → P := fun p ↦ p

example : P → (P → Q) → Q := fun p h ↦h p
 
example : Q → (P → Q) := fun q _ ↦ q

example : P ∧ Q → P := fun ⟨p, _⟩ ↦ p

example : P ∧ Q → Q := fun ⟨_, q⟩ ↦ q

example : P → Q → (P ∧ Q) := fun p q ↦ ⟨p, q⟩

example : P → P ∨ Q := fun p ↦ Or.inl p

example : Q → P ∨ Q := fun q ↦ Or.inr q

example : (P → R) → (Q → R) → (P ∨ Q → R) := fun h h' ↦ fun
  | Or.inl p => h p
  | Or.inr q => h' q

example : True := True.intro

example : P → True := fun _ ↦ True.intro

example : False → P := False.elim

example : (True → False) → False := fun h ↦ h True.intro

example : (P → False) → ¬P := fun h ↦ h

example : (P → Q) → (¬Q → ¬P) := fun h nq p ↦ nq (h p)