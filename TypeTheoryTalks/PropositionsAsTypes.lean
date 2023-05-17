/-!
# Propositions as Types

Type theory is a theory where types and their constructions are the building blocks.
The rules of logic can (surprisingly) be interpreted as special cases of these general type-theoretic constructions.

This file introduces the *Curry-Howard correspondence*, a deep link between propositions and types.
-/

variable (α β γ : Type) (P Q R : Prop)

section Functions

example (a : α) (f : α → β) : β := sorry

end Functions

section Implication

example (p : P) (φ : P → Q) : Q := sorry

end Implication

section Products

example (a : α) (b : β) : α × β := sorry

example (t : α × β) : α := sorry

example (t : α × β) : β := sorry

end Products

section Conjunction

example (p : P) (q : Q) : P ∧ Q := sorry

example (t : P ∧ Q) : P := sorry

example (t : P ∧ Q) : Q := sorry

end Conjunction


section Disjunction

end Disjunction

section DisjointUnion

end DisjointUnion

section TrueFalse

end TrueFalse