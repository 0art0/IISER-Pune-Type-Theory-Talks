import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Real.Basic

/-!
# An introduction to type theory and interactive theorem provers

Just as set theory is centered around "sets" and "elements", type theory is centered around "types" and "terms".

In type theory, every term has a *unique* associated type. This is in contrast with set theory, where elements can belong to multiple sets.

`Lean` allows us to see the type associated with a term using the `#check` command.
-/

section Types

#check 1
#check true

#eval (1 : ℤ) - 3
#check 5 * (4 + 2)
#check true && false
#check true || !(false && true)

def n := 2
#check n

def b := false
#check b

#check ℕ
#check Bool
#check ℤ

#check Type
#check ℕ → Type

end Types

/-!
## Function types

Unlike set theory, functions are a primitive notion in type-theoretic foundations. 
Corresponding to types `A` and `B`, there is a function type `A → B` whose terms are functions from `A` to `B`.
-/

#check Nat.succ -- ℕ → ℕ

/-! ### Function abstraction 
Functions in type theory are created by *function abstraction*, 
which involves specifying a "rule" for transforming an arbitrarily chosen variable in the domain to a term of the co-domain.
-/

#check fun x ↦ x + 2  -- ℕ → ℕ

def f : ℕ → ℕ := fun n ↦ n * 5

#check f

def g (n : ℕ) : ℕ := 2 * n + 3 

#check g

def h (a b : ℕ) := a ^ 2 + b ^ 2

#check h

/-! ### Function evaluation 
In `Lean`, brackets around the arguments of functions are typically omitted.
A function `f : A → B` applied to an argument `a : A` looks like `f a` rather than `f(a)`.
-/

#eval (fun x ↦ x + 2) 4  -- 6

#eval f 12

#eval g 3

#eval h 1 2

/-! ### Currying 
In type theory, all functions take in a single argument by default. 
The effect of multi-argument functions is simulated through *currying*, which
takes in arguments one at a time instead of all at once.
-/

#check h 1

variable (A B C : Type)

def curry : ((A × B) → C) → (A → B → C) := sorry

def uncurry : (A → (B → C)) → ((A × B) → C) := sorry

/-! ### Dependent function types 
Dependent type theory also supports *dependent functions*, where
the type of the co-domain is allowed to depend on the input.
-/

def zeroVec : (n : ℕ) → Vector ℝ n := sorry