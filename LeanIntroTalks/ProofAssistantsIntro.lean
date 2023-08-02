import LeanSlides
import Mathlib.Tactic
import ProofWidgets.Demos.Rubiks
import ProofWidgets.Demos.Conv
import ProofWidgets.Component.Plotly
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
#eval sumUpto 5

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
- Deriving new mathematical insights through formalisation
-/

/-! ## The Lean mathematics library - `mathlib` -/
#html iframeComponent 
  "https://leanprover-community.github.io/mathlib4_docs/"

#slides +draft Future /-!

# The future of proof assistants

While it is remarkable that 
this technology exists at all,
proof assistants fall short of their promise
to genuinely assist in mathematical proofs.

---

There are two ways to close the gap between 
formal mathematics and mathematical practice:
- From below, by developing better 
  automation, interfaces and tooling
- From above, by developing new abstractions and
  recasting mathematical theories to make them
  more amenable to formalisation
-/

#slides +draft Automation /-!

## Automation of "routine proofs"

Good automation for reasoning steps that are
mathematically "routine" would go a long way
in making proof assistants more usable.

Such automation should ideally also be
deterministic, transparent and reliable.

---

Automation for routine proofs can have a 
number of benefits aside from making formalisation easier:
- Searching vast libraries
- Translation and auto-formalisation
- Developing stronger automation

## Domain-specific automation

A number of algorithms have been developed
for automating specific mathematical problems,
such as computing roots of polynomials or symbolic integration.

Integrating such tools with a proof assistant
would assist in formalising and discovering proofs.

-/

/-- An example of the `polyrith` tactic in action. -/
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) : 
    x*y = -2*y + 1 := by
  sorry
  -- polyrith

#slides +draft InterfacesTooling /-!

## Interfaces and tooling 

As proof assistants are 
meant to be used interactively,
having a good user interface 
will reduce friction while proving theorems.

Tools to suggest steps and proof strategies
would allow mathematicians to use proof assistants as
"digital chalkboards" for discovering new mathematics.

-/

/-- An interface for targeted rewriting with `conv`. -/
example : ∀ (a b c d : ℕ), a = b → c + a + d = c + b + d := 
  by with_panel_widgets [ConvPanel]  
    intros a b c d h
    conv => {}
    sorry


/-- Data for a histogram rendered within Lean. -/
def histData := [1, 1, 5, 5, 3, 4, 4, 4, 5, 1, 2, 2, 3, 3, 5]
open scoped ProofWidgets.Jsx ProofWidgets.Json in
#plot {
  data: [{
    x: $(histData),
    type: "histogram"
  }],
  layout: {
    title: "A sample histogram",
    xaxis: { title: "Bins" },
    yaxis: { title: "Count" }
  },
  config: {
    scrollZoom: true,
    editable: true
  }
}

#slides +draft Mathematics /-!

## Improving foundations

Mathematical foundations make it possible to 
syntactically encode mathematical ideas.

It is worth investigating new foundations that
make it possible to encode mathematics *conveniently*.

Ideally, a foundation should make precise all
the informal heuristics used in practice.

## New mathematical abstractions and theories

Mathematical abstractions help unify
notions that are superficially similar,
and typically lend themselves to formalisation
more easily.

For example, Bourbaki's theory of filters 
unifies the various kinds of limits in analysis.

-/

#slides +draft Exposition /-!

## Exposition

Libraries of formal mathematics are 
valuable mathematical resources, containing
a vast amount of mathematics formalised in a
consistent and inter-compatible way.

It should be possible to directly interact with
and learn from the material in these libraries.
-/

/-! A demonstration of a tool to generate 
  informal interactive explanations from formal proofs.-/
#html iframeComponent 
  "https://www.imo.universite-paris-saclay.fr/~patrick.massot/Examples/ContinuousFrom.html"

/-! Interactive visualisations in Lean -/
open scoped ProofWidgets.Jsx in
#html <Rubiks seq={#["L", "L", "D⁻¹", "U⁻¹", "L", "D", "D", "L", "U⁻¹", "R", "D", "F", "F", "D"]} />

#slides +draft AI /-!

## Artificial intelligence and mathematics

Recent advances in artificial intelligence,
particularly the development of large language models (like ChatGPT),
hold enormous promise for integration with proof assistants.

---

Large language models can be used to:
- Auto-formalise mathematics into Lean
- Search and answer questions about results in the library
- Suggest various tactic and code completions

-/

/-! A demonstration of `LeanAIde`, 
  a statement auto-formalisation tool for Lean. -/
open scoped ProofWidgets.Jsx in
#html <img src="../Presentations/src/.img/leanaide-mathlib4.gif" />

#slides +draft Conclusion /-!

## Proof assistants

> Interactive theorem provers are tools that can help mathematicians to
experiment, discover, create, automate, verify, communicate and understand mathematics.

## Proof assistants as general mathematical software?

Since some theorem provers are also 
efficient and general-purpose programming languages,
it is possible to integrate them with the capabilities of
other kinds of mathematical software.


## Conclusion

- Proof assistants hold great promise in changing the way mathematics is done
- Improvements in mathematical foundations, proof automation and 
  artificial intelligence will go a long way in making this technology more usable
- Overall, interactive theorem provers point towards a future of 
  fruitful mathematical collaborations between humans and computers.

## Resources

Some resources for learning Lean:
- [The Natural Number Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4)
- [Mathematics in Lean 4](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/title_page.html)
- [Functional Programming in Lean 4](https://leanprover.github.io/functional_programming_in_lean/)
- [Meta-Programming in Lean 4](https://github.com/leanprover-community/lean4-metaprogramming-book)
- [The Lean community Zulip](https://leanprover.zulipchat.com/)

-/