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

example : P → P := by
  intro p
  exact p

example : P → (P → Q) → Q := by
  intro p h
  apply h
  exact p
 
example : Q → (P → Q) := by
  intro q _
  exact q

example : P ∧ Q → P := by
  intro ⟨p, _⟩
  exact p

example : P ∧ Q → Q := by
  intro ⟨_, q⟩
  exact q

example : P → Q → (P ∧ Q) := by
  intro p q
  exact ⟨p, q⟩

example : P → P ∨ Q := by
  intro p
  apply Or.inl
  exact p

example : Q → P ∨ Q := by
  intro q
  apply Or.inr
  exact q

example : (P → R) → (Q → R) → (P ∨ Q → R) := by
  intro h h' hpq
  match hpq with
    | Or.inl p =>
      apply h
      exact p
    | Or.inr q =>
      apply h'
      exact q

example : True := by exact True.intro

example : P → True := by
  intro _
  exact True.intro

example : False → P := by exfalso

example : (True → False) → False := by
  intro h
  apply False.elim
  apply h
  exact True.intro

example : (P → False) → ¬P := by
  intro h
  exact h

example : (P → Q) → (¬Q → ¬P) := by
  intro h
  intro nq
  intro p
  apply nq
  apply h
  exact p