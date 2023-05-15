import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupPower.Basic

/-
# International Mathematical Olympiad 1964, Problem 1b
Prove that there is no positive integer n for which 2^n + 1 is divisible by 7.
-/
theorem imo_1964_q1b : ∀ (n : ℕ), (2 ^ n + 1) % 7 ≠ 0
  | 0 | 1 | 2 => by decide
  | n + 3 => by
    rw [pow_add, Nat.add_mod, Nat.mul_mod, show 2 ^ 3 % 7 = 1 by rfl]
    simp [imo_1964_q1b n]