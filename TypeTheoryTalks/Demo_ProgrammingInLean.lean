import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import ProofWidgets.Demos.Rubiks
import Aesop
import Lean

/-!
# Programming and Metaprogramming in Lean4

*Lean4* is designed from the ground-up as a fast and efficient general-purpose functional programming language.

This file gives an overview of some of the capabilities of Lean4 as a programming languauge.
-/

section HelloWorld

  /-!
  ## Hello World

  Printing a standard "Hello, world!" message.
  -/

def helloWorld : IO Unit := 
  IO.println "Hello, world!"

#eval helloWorld

end HelloWorld

namespace Sorting

  /-!
  ## Programs with proofs

  A demonstration of a simple sorting algorithm with proof, 
  loosely inspired by https://github.com/IPDSnelting/tba-2022/blob/master/TBA/AesopSort.lean.
  -/

variable {α : Type _} [LinearOrder α] [DecidableRel <| LE.le (α := α)]

/-- The definition of a sorted list. -/
@[simp] def isSorted : List α → Prop
  | [] => True
  | [a] => True
  | a :: b :: tail => a ≤ b ∧ isSorted (b :: tail)

/-- Insert an element into a list according to the order. -/
@[simp] def insertInOrder (a : α) : List α → List α
  | [] => [a]
  | h :: tail => 
    if a ≤ h then 
      a :: h :: tail 
    else 
      h :: (insertInOrder a tail)   

/-- A simple sorting algorithm based on insertion sort. -/
@[simp] def insertionSort : List α → List α
  | [] => []
  | h :: tail => insertInOrder h (insertionSort tail)

#eval insertionSort [4, 3]
#eval insertionSort [1, 2349, 2, 21, 3, 0, 12, 33, 30, 54]

attribute [simp] le_of_not_le
attribute [-simp] not_le

/-- Inserting an element in a sorted list leaves the result sorted. -/
lemma sorted_insertInOrder (l : List α) (hyp : isSorted l) (a : α) : isSorted (insertInOrder a l) := by
  induction l with
    | nil => simp
    | cons h t ih => 
      match t with
        | .nil => 
          by_cases c:a ≤ h
          · simp [c]
          · simp [c] 
        | .cons h' t' =>
          by_cases c:a ≤ h
          · simp [c]
            exact hyp
          · simp [c]
            by_cases c':a ≤ h'
            · simp [c']
              simp at hyp
              exact ⟨le_of_not_le c, hyp.right⟩
            · simp [c']
              simp [c'] at ih
              simp at hyp
              exact ⟨hyp.left, ih hyp.right⟩

/-- The output of `insertionSort` is sorted. -/
theorem sorted_insertionSort (l : List α) : isSorted (insertionSort l) := by
  induction l with
    | nil => simp
    | cons h t ih => 
      simp
      apply sorted_insertInOrder
      exact ih

end Sorting

section FunctionalProgramming

  /-!
  ## An example of functional programming in Lean4

  Lean is an example of a [*functional programming language*](https://en.wikipedia.org/wiki/Functional_programming).

  Consider the following artifical problem:
  **How many powers of `2` less than `2^16` have a decimal expansion that ends in `2`?**

  While this can be solved in typical functional programming style, Lean also supports an imperative Python-like syntax which
  is automatically translated to functional style code. 
  -/

def pow2Count : Nat := Id.run do
  let mut count : Nat := 0
  for n in [0:16] do
    let a := 2 ^ n
    if a % 10 = 2 then
      count := count + 1
  return count

#eval pow2Count

def pow2Count' :=
  List.range 16 |>.map (2 ^ ·) |>.filter (· % 10 = 2) |>.length

#eval pow2Count'

end FunctionalProgramming

section Syntax

  /-!
  ## Syntax in Lean4

  Being a interactive theorem prover meant for mathematics, Lean supports a rich and extensible syntax framework. 
  -/

#check { x : Nat // x ≤ 1 }


macro "The function that sends " x:ident " : " T:term " to the value " v:term : term =>
  `(fun $x : $T ↦ $v)

#eval (The function that sends n : Nat to the value n + 5) 2

end Syntax

section SymbolicAlgebra

  /-!
  ## Symbolic Algebra

  Lean can be extended to interface with external symbolic algebra softwares to perform 
  *unverified* symbolic algebra calculations from the Lean editor.
  -/

open Lean Elab Term Meta Tactic

declare_syntax_cat arith
syntax str : arith
syntax ident : arith
syntax num : arith
syntax arith "+" arith : arith
syntax arith "-" arith : arith
syntax arith "*" arith : arith
syntax arith "/" arith : arith
syntax arith "^" arith : arith
syntax "(" arith ")" : arith

def arithToString : TSyntax `arith → String :=
  fun stx ↦stx.raw.reprint.get! 

open IO.Process in -- code by Max Nowak from https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/external.20process/near/345090183
/-- Pipe input into stdin of the spawned process, then return output upon completion. -/
def cmd_with_stdin (args : SpawnArgs) (input : String) : IO Output := do
  let child <- spawn { args with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) <- child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout <- IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr <- child.stderr.readToEnd
  let exitCode <- child.wait
  let stdout <- IO.ofExcept stdout.get
  return { exitCode, stdout, stderr }

def queryPari (a : TSyntax `arith) : IO String := do
  let out ← cmd_with_stdin 
              { cmd := "gp", args := #["-q"]} 
              <| arithToString a
  return out.stdout

elab "#symbolic" e:arith : command => do
  let out ← queryPari e
  logInfo out

#symbolic 2 + 2                    -- 4
#symbolic (x ^ 2 - 1) / (x + 1)    -- x - 1
#symbolic (x + 2) * (8 * x + 17)   -- 8*x^2 + 33*x + 34

end SymbolicAlgebra

section IO

  /-!
  ## IO in Lean4
  Lean4 also supports standard IO operations like generating random numbers and reading/writing files.
  -/

/-- A randomly generated natural number. -/
def randomNum : IO Nat := IO.rand 0 25

#eval randomNum


open Lean in
/-- A script for collecting the docstrings in the current file. -/
def getDocstrings : MetaM <| List String := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? env.mainModule
  env.constants.toList.filterMapM <| fun ⟨nm, _⟩ ↦ do
    if env.getModuleIdxFor? nm = modIdx then
      findDocString? env nm
    else pure none

#eval getDocstrings

end IO

section Tactics

  /-!
  ## Tactics

  Lean allows proof automation via tactics. 
  Lean's tactic framework is highly extensible, allowing users to implement their own automation.
  -/

example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

open Lean Elab Term Tactic in
elab "trace_goal" : tactic => do
  let mainGoal ← getMainGoal 
  logInfo m!"The goal is {mainGoal}"

example : 1 = 1 := by
  trace_goal
  rfl

end Tactics

section Widgets
  /-!
  ## User Widgets
  Lean supports a framework of interactive and extensible *user widgets* for visualisation.
  -/

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

#html <Rubiks seq={eg} />

end Widgets

section Showcase

  /-!
    ## Showcase

    There are several exciting projects that use Lean4 as a programming language in novel ways.
    Some of these are:
    - [Fxy](https://github.com/arthurpaulino/FxyLang) - A custom programming language within Lean4
    - [SciLean](https://github.com/lecopivo/SciLean) - Scientific computation in Lean4
    - [Lean4-RayTracer](https://github.com/kmill/lean4-raytracer) - A raytracer in Lean4
    - [Aesop](https://github.com/JLimperg/aesop) - An automation tool for Lean4
    - [ProofWidgets4](https://github.com/EdAyers/ProofWidgets4) - Interactive visualisations in Lean4
    - [SATurn](https://github.com/siddhartha-gadgil/Saturn) - A proved implementation of a SAT solver in Lean4
    - [Lean4 Balance Car](https://github.com/GaloisInc/lean4-balance-car) - Robotics in Lean4
    - [LeanAIde](https://github.com/siddhartha-gadgil/LeanAide) - Automatic translation from natural language to Lean4
    - [Lean4 Maze](https://github.com/dwrensha/lean4-maze) - A maze game in Lean4
    - [Lean To](https://github.com/bollu/lean-to) - Experimental Jupyter notebook interface for Lean4
    - [GAP Lean](https://github.com/opencompl/lean-gap) - A GAP embedding in Lean4
    - [Lean Loris](https://github.com/siddhartha-gadgil/lean-loris) - Experiments in forward reasoning in Lean4 
  -/

end Showcase