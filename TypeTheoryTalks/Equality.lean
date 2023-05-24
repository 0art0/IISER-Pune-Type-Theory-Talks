/-!
Somewhat counter-intuitively, equality is not a primitive notion in Martin-Löf Type Theory, but
rather defined within the theory as an inductive type.

Intuitively, it is defined as the "smallest reflexive relation" on a type (source: https://twitter.com/andrejbauer/status/1383803239947128843?s=20).

The content here is loosely inspired by https://xenaproject.wordpress.com/2021/04/18/induction-on-equality/.
-/

inductive Equals {α : Sort _} : α → α → Prop
  | refl : (a : α) → Equals a a

infix:50 " ∼ " => Equals -- type with `\sim`

namespace Equals

variable {α : Sort _} {a b c : α}

theorem ind (R : α → α → Prop) (hR : ∀ x : α, R x x) : ∀ {a b : α}, a ∼ b → R a b :=
  fun h ↦ Equals.rec (hR _) h

example : a ∼ a := refl a

theorem symm : ∀ {a b : α}, a ∼ b → b ∼ a :=
  ind (fun a b ↦ b ∼ a) refl

theorem trans : ∀ {a b c : α}, a ∼ b → b ∼ c → a ∼ c :=
 fun hab ↦ (ind (fun a b ↦ ∀ {c}, b ∼ c → a ∼ c) <| fun _ ↦ id) hab

end Equals