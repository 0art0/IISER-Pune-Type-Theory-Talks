import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import ProofWidgets.Component.HtmlDisplay
import Lean

/-!
# The `Lean` theorem prover

Lean 4 is designed to be both
an interactive theorem prover as
well as an efficient programming language.

---

This file demonstrates examples of
how Lean can be used to prove theorems and
programs, including how they can be combined.
Some examples of meta-programming are also included.
-/


section SumUpto

/-- `sumUpto n` is the sum of the natural numbers upto (and including) `n`. -/
def sumUpto : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumUpto n

#eval sumUpto 5

/-- The `sumUpto` function written using Python-like syntax. -/
def sumUpto' (n : ℕ) : ℕ := Id.run do
  let mut sum := 0
  for i in [0:n+1] do
    sum := sum + i
  return sum

#eval sumUpto' 10

/-! Custom notation for the `sumUpto` function. -/

notation "The sum of the first " n " natural numbers" => sumUpto n

#eval The sum of the first 10 natural numbers

/-! Different custom notation for the `sumUpto` function. -/

macro "∑ " head:ident " ∈ " "["start:num ":" stop:num "]" "," body:term : term => 
  `(term| Id.run do
    let mut sum := 0
    for i in [$start:num:$stop:num] do
      sum := sum + (fun $head:ident ↦ $body) i
    return sum)

#eval ∑ i ∈ [0:11], i

end SumUpto


section LinearDiophantineEquations

/-!

# Linear Diophantine equations

A linear Diophantine equation is one of the form
`a * x + b * y = c`,
where `a`, `b` and `c` are known integers and
`x` and `y` are variables over the integers.

---

It turns out that a linear Diophantine equation has a solution
if and only if `gcd a b` divides `c`.
- If a Diophantine equation has a solution, then 
  since `gcd a b` divides `a` and `b`, it divides
  `a * x + b * y = c`.
- Conversely, if `gcd a b` divides `c`, by
  Bezout's lemma there are integers `x` and `y` such that
  `a * x + b * y = gcd a b`; writing `c = d * gcd a b`, 
  the integers `d * x` and `d * y` satisfy the Diophantine equation
  with constants `a`, `b` and `c`.
-/

section Widget

open Lean ProofWidgets

set_option maxHeartbeats 999999999

def sliderDiophantineWidget : String := 
  let contents : IO String := do
    let child ← IO.Process.spawn {
      cmd := "curl",
      args := #["-L", "https://raw.githubusercontent.com/0art0/IISER-Pune-Type-Theory-Talks/main/LeanIntroTalks/sliderDiophantine.js"]
      stdout := .piped
    }
    let stdout ← IO.asTask child.stdout.readToEnd .dedicated
    IO.ofExcept stdout.get
  contents.run' () |>.get!

structure NoProps where
deriving Server.RpcEncodable

@[widget_module]
def LinearDiophantine : Component NoProps where
  javascript := sliderDiophantineWidget

open scoped ProofWidgets.Jsx in
#html <LinearDiophantine />

end Widget

#check Int.gcd_eq_gcd_ab -- ∀ (x y : ℤ), ↑(Int.gcd x y) = x * Int.gcdA x y + y * Int.gcdB x y

#check Int.gcd_dvd_left -- ∀ (i j : ℤ), ↑(Int.gcd i j) ∣ i
#check Int.dvd_mul_right -- ∀ (a b : ℤ), a ∣ a * b
#check dvd_add /-∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [inst_2 : LeftDistribClass α] {a b c : α},
  a ∣ b → a ∣ c → a ∣ b + c-/


#check Int.mul_ediv_cancel_of_emod_eq_zero -- ∀ {a b : ℤ}, a % b = 0 → b * (a / b) = a
#check Int.emod_eq_zero_of_dvd -- ∀ {a b : ℤ}, a ∣ b → b % a = 0

/-- The Diophantine equation `a * x + b * y = c` has a solution
    if and only if `gcd a b` divides `c`. -/
lemma eqn_solvable_iff_divides_gcd (a b c : ℤ) :
    (∃ x : ℤ, ∃ y : ℤ,  a * x + b * y = c) ↔  ↑(Int.gcd a b) ∣ c := by
  sorry

/-- Solvability of linear Diophantine equations is a decidable problem. -/
instance : Decidable (∃ x : ℤ, ∃ y : ℤ,  a * x + b * y = c) := 
  sorry

end LinearDiophantineEquations