import Aesop
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Algebra.Group.Basic

section PropositionalLogic

/-!
## Propositional logic using `Aesop`

`Aesop` can prove routine theorems in
propositional logic automatically.
-/

variable (P Q R : Prop)


example : P → P := by aesop

example : P → (Q → P) := by aesop

example : P ∧ Q → P ∨ Q := by aesop

example : P ∨ P ↔ P ∧ P := by aesop

example : (P → Q) → (¬Q → ¬P) := by aesop

example : (P ∨ Q)  ↔  (Q ∨ P) := by aesop

example : (P ∧ Q) → R  ↔  P → (Q → R) := by aesop

example : (P → (Q → R)) → ((P → R) → (P → R)) := by aesop

end PropositionalLogic

section TrivialLemmas

/-!

## Proving trivial lemmas with `Aesop`

`Aesop` uses Lean's simplifier internally, which
allows it to prove trivial lemmas by simplification.

-/

example {a b : ℕ} (h₁ : a = 5) (h₂ : b = 2 + 3) : a = b :=
  by aesop

example {a : ℕ} : a + 0 = 0 → a = 0 + 0 := by aesop

example {G : Type} [Group G] {g : G} : 1⁻¹ * 1 = g * 1 * g⁻¹ :=
  by aesop

example : [1, 2, 3] ≠ [] := by aesop

example {l : List α} {a : α} : a ∈ l → l ≠ [] := by aesop

end TrivialLemmas

/-!

## An example of `Aesop` proof search

The lemma `Nat.max_eq_zero_iff` in `Mathlib` states that if the 
maximum of two natural numbers is zero, then one of them must be zero.

This is a straightforward proof that crucially rests on the fact that
the natural numbers form a total order, i.e., that `∀ m n : ℕ, m ≤ n ∨ m ≥ n`.

This file demonstrates how the `Mathlib` proof, which is around `9` lines long,
can be automated by an `aesop` invocation with the appropriate configuration.

This is an example of how a verbose proof can be replaced by 
a proof search with just the core details of the proof specified. 
-/

-- As the lemma in `Mathlib` is tagged with `simp`, 
-- `Aesop` can find the proof instantly if this attribute is not removed.
attribute [-simp] Nat.max_eq_zero_iff

theorem max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro h
    cases' le_total m n with H H
    · simp only [H, max_eq_right] at h
      exact ⟨le_antisymm (H.trans h.le) (zero_le _), h⟩
    · simp only [H, max_eq_left] at h
      exact ⟨h, le_antisymm (H.trans h.le) (zero_le _)⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem max_eq_zero_iff' : max m n = 0 ↔ m = 0 ∧ n = 0 := by
  aesop (add unsafe forward [le_total])

