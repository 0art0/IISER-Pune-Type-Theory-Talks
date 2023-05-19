/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
Modified by: Anand Rao
-/
-- Based on `kbuzzard/IIScExperiments`: https://github.com/kbuzzard/IISc-experiments/blob/main/IIScExperiments/GroupTheory.lean

import Mathlib.Algebra.Group.Basic

/-! A minimal definition of a group (with multiplicative notation) as a Lean typeclass. -/
class Group' (G : Type) extends One G, Mul G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

#check Group'

/-!
The list of group axioms is shorter than what one would typically see, 
since the remaining two are in fact consequences of the above.
-/

namespace Group'

/-! Let `G` be a group, and let `a`, `b` and `c` be elements of `G`. -/
variable {G : Type} [Group' G] {a b c : G}

lemma mul_left_cancel (h : a * b = a * c) : b = c := by
  have h' : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    rw [h]
  rw [← mul_assoc, ← mul_assoc, inv_mul_self, one_mul, one_mul] at h'
  exact h'

lemma mul_eq_of_eq_inv_mul (h : a⁻¹ * c = b) : a * b = c := by
  rw [← one_mul b, ← inv_mul_self a, mul_assoc] at h
  symm
  exact mul_left_cancel h

/-- One of the two missing group axioms -/
lemma mul_one (a : G) : a * 1 = a := by
  apply mul_eq_of_eq_inv_mul
  exact inv_mul_self a

/-- The other missing group axiom -/
lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  exact mul_one _

section Simplifier

/-!
This section demonstrates an example of developing 
domain/problem-specific proof automation in Lean via the extensible `simp` tactic.

The `simp` tactic is an *equational simplifier* - given a list of equations and a goal, `simp` attempts to 
replace occurrences of the left-hand side of any of the equations in the goal with the corresponding right-hand side.
-/

attribute [simp] one_mul mul_one inv_mul_self mul_inv_self mul_assoc

/-!
In addition to supplying the five group axioms to the simplifier, we will need to supply a few more lemmas to make the 
rewrite set *confluent*. For example, the expression `(a⁻¹ * a) * b` can be simplified using `inv_mul_self`
and then `one_mul` to `b`; however, if one uses `mul_assoc` first, it changes to `a⁻¹ * (a * b)` and does not simplify further.
The list of remaining lemmas needed to make the rewrite system confluent come from the [*Knuth-Bendix algorithm*](https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm).
-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc]
  simp

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  simp

lemma left_inv_eq_right_inv {a b c : G} (h₁ : b * a = 1) (h₂ : a * c = 1) : 
    b = c := by
  calc b = b * 1       := by simp
      _  = b * (a * c) := by rw [h₂]
      _  = (b * a) * c := by simp
      _  = 1 * c       := by rw [h₁]
      _  =  c          := by simp

lemma mul_eq_one_iff_eq_inv : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  · intro h
    exact left_inv_eq_right_inv (inv_mul_self a) h
  · intro h
    rw [← h]
    simp

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 := by
  rw [← mul_eq_one_iff_eq_inv]
  simp

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a := by
  rw [← mul_eq_one_iff_eq_inv]
  simp  

@[simp] lemma mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
 rw [← mul_eq_one_iff_eq_inv] 
 simp

/-! An example of the simplifier in action. -/
example (G : Type) [Group' G] (a b : G) : 
  (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a⁻¹⁻¹⁻¹⁻¹ = 1 := by simp

end Simplifier

section Bonus

/-- If the square of every group element is trivial, then the group itself is Abelian. -/
example (G : Type) [Group' G] (hyp : ∀ g : G, g * g = 1) :
    ∀ g h : G, g * h = h * g := by
  have hyp' : ∀ a : G, a⁻¹ = a := by
    intro a
    rw [← mul_eq_one_iff_eq_inv]
    exact hyp _
  intro g h
  calc g * h = g⁻¹ * h⁻¹ := by simp [hyp']
        _    = (h * g)⁻¹ := by simp
        _    = h * g     := by rw [hyp']

end Bonus