import Mathlib.Tactic

/-!
Logic exercises using Lean's tactic mode, which allows proofs to be constructed interactively.

Some useful tactics are:
- `intro`, which introduces an assumption in the context. This tactic is used when the goal is a function type.
- `apply`, which acts on a goal of the form `⊢ Q` using a function with type `P → Q` to produce a new goal `P`.
- `exact`, a less flexible variant of `apply` that is used to finish proofs. The tactic `exact q` completes a proof when the goal has type `⊢ Q`.
- `cases`, to break an assumption into the relevant cases.
- `trivial`, to prove `True`.
- `exfalso`, to construct a function from `False`.
-/

variable (P Q R : Prop)

example : P → P := by sorry

example : P → (P → Q) → Q := by sorry
 
example : Q → (P → Q) := by sorry

example : P ∧ Q → P := by sorry

example : P ∧ Q → Q := by sorry

example : P → Q → (P ∧ Q) := by sorry

example : P → P ∨ Q := by sorry

example : Q → P ∨ Q := by sorry

example : (P → R) → (Q → R) → (P ∨ Q → R) := by sorry

example : True := by sorry

example : P → True := by sorry

example : False → P := by sorry

example : (True → False) → False := by sorry

example : (P → False) → ¬P := by sorry

example : (P → Q) → (¬Q → ¬P) := by sorry