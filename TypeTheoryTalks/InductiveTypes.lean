import Mathlib.Data.Vector.Basic

/-!

# Inductive types

Inductive types are one of the fundamental building blocks in type theory.

Defining an inductive type automatically generates the following:
- A constant for each constructor
- A proof that the constructors are disjoint
- A proof that the constructors are injective
- An *induction principle*.

-/

#check Nat

#check Nat.zero
#check Nat.succ
#check Nat.rec
#check Nat.noConfusion


#check Bool

-- An example of defining a function by recursion.
def Bool.and : Bool → (Bool → Bool) :=
  fun b₁ ↦
    match b₁ with
      | true =>
          fun b₂ => 
            match b₂ with
              | true => true
              | false => false
      | false => 
          fun _ ↦ false

-- The same function with better syntax
def Bool.and' : Bool → Bool → Bool
  | false, _ => false
  | true, b => b

#eval Bool.and true true

#check Bool.and_false

#eval Bool.and' false false


#check Unit

#check True


#check Empty

#check False

/-! Some types that are useful in mathematics and proofs. -/
#check Prod

#check Sum

#check @Sum.rec

/-! Some types that are useful in programming. -/

#check List

def List.map' (f : α → β) (base : List β) : List α → List β
  | [] => base
  | a :: as => f a :: (List.map' f base as)

#eval [1, 2, 3].map' (fun n ↦ n + 3) [21748973432, 34085043932546]

#check Vector