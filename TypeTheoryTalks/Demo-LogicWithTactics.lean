import Mathlib.Tactic

/-!
Logic exercises using Lean's tactic mode.
-/

variable (P Q R : Prop)

example : P → P := by sorry

example : P → (P → Q) := by sorry
 
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