import Mathlib.Data.Nat.Basic

/-!
# An introduction to type theory and interactive theorem provers

Just as set theory is centered around "sets" and "elements", type theory is centered around "types" and "terms".

In type theory, every term has a *unique* associated type. This is in contrast with set theory, where elements can belong to multiple sets.

`Lean` allows us to see the type associated with a term using the `#check` command.
-/

section Types

#check 1
#check true

#check 1 + 3
#check 5 * (4 + 2)
#check true && false
#check true || !(false && true)

def n : ℕ := 2
#check n

def b : Bool := false
#check b

#check ℕ
#check Bool

#check Type

end Types

/-!
## Function types

Functions are central to type theory. 
-/

-- Function types

-- Function abstraction

-- Function evaluation

-- Currying

/-!
## Product types

-/

-- Product types

-- Creating

-- Projections

/-!
## Dependent types


-/