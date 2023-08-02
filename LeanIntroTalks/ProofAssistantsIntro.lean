import LeanSlides
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import ProofWidgets.Demos.Rubiks
import ProofWidgets.Demos.Plotly
import Aesop
import Lean

/-!
# Proof Assistants : History, Ideas and Future
-/

#slides +draft Intro /-!
% Proof Assistants: History, Ideas and Future
% IISER Pune
% 2nd August, 2023

---

![An earlier article by Herman Geuvers](https://github.com/0art0/IISER-Pune-Type-Theory-Talks/blob/main/.img/proof-assistants-history-ideas-future.png?raw=true)

## Talk outline

- An introduction to interactive theorem provers
- An overview of what has been accomplished so far
- Speculation about the future role 
  of interactive theorem provers 
  in pure mathematics research.

# Proof assistants

> An interactive theorem prover (or proof assistant) is a kind of mathematical technology for constructing and verifying formal mathematical proofs. 

## Mathematical software

- **Numerical analysis and statistics**: `R`, `MATLAB`, `numpy`, ...
- **Symbolic algebra**: `SageMath`, `Maple`, `Magma`, ...
- **Communication and publication**: $\LaTeX$
- **Mathematical reasoning**: `Lean`, `Agda`, `Coq`, ...

## Modern proof assistants

- Isabelle
- PVS
- Coq
- Lean
- Agda
- Mizar
- Metamath
- HOL Light

## `Lean`

- `Lean` is an interactive theorem prover and programming language 
  based on the foundation of dependent type theory.
- It is being developed primarily by 
  Leonardo de Moura and Sebastian Ullrich.
- `Lean` has a large library of formal mathematics, 
  known as mathlib.
- `Lean4` is also designed to be a 
  fast and general-purpose programming language.
- Lean is common platform for programs and proofs, 
  allowing them to be mixed in novel ways.

-/

/-- `sumUpto n` is the sum of the natural numbers upto (and including) `n`. -/
def sumUpto : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumUpto n

/-! A proof of a standard identity. -/
theorem sumUpto_eq : ∀ n : ℕ, 2 * sumUpto n = n * (n + 1) := by
  sorry

/-! ## The raw proof term -/
-- set_option pp.proofs true in
-- set_option pp.raw.maxDepth 10 in
-- #reduce sumUpto_eq

/-! ## Computing with `sumUpto` -/
-- #eval sumUpto 100

#slides +draft Formalisation /-!

# Formalisation

With expressive syntax and the facility to 
build up proofs interactively at a high level,
modern proof assistants are beginning to make the 
large-scale formalisation of mathematics practical.

## Libraries of formal mathematics

- Lean's `mathlib`
- Isabelle's `Archive of Formal Proofs`
- Coq's `Mathematical Components` library
- The `Mizar Mathematical Library`
- The `Agda-UniMath` library

## Notable formalisations

- The Jordan curve theorem
- The Prime Number theorem
- The Kepler conjecture
- The Odd-order theorem
- The central theorem of condensed mathematics
- Sphere eversion

## Benefits of formalisation

- Checking consistency and validity of mathematical arguments
- Formally verifying hardware and software
- Organising mathematical knowledge

-/

/-! ## The Lean mathematics library - `mathlib` -/
#html iframeComponent 
  "https://leanprover-community.github.io/mathlib4_docs/"
