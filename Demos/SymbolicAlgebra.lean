 import Lean
  import Mathlib.Algebra.Ring.Basic
  import Mathlib.Tactic.Basic
  import Mathlib.Tactic.Ring
  import Mathlib.Tactic.NormNum
  import Mathlib.Tactic.Linarith

  open Lean Elab Term Meta Tactic

  declare_syntax_cat arith
  syntax ident : arith
  syntax num : arith
  syntax arith "+" arith : arith
  syntax arith "-" arith : arith
  syntax arith "*" arith : arith
  syntax arith "/" arith : arith
  syntax arith "^" arith : arith
  syntax "(" arith ")" : arith

  partial def arithToString : TSyntax `arith → String
    | `(arith| $a:ident) => toString a.getId
    | `(arith| $n:num) => toString n.getNat
    | `(arith| $a + $b) => s!"{arithToString a} + {arithToString b}"
    | `(arith| $a - $b) => s!"{arithToString a} - {arithToString b}"
    | `(arith| $a * $b) => s!"{arithToString a} * {arithToString b}"
    | `(arith| $a / $b) => s!"{arithToString a} / {arithToString b}"
    | `(arith| $a ^ $b) => s!"{arithToString a} ^ {arithToString b}"
    | `(arith| ($a)) => s!"({arithToString a})"      
    | _ => panic! "Invalid `arith` syntax"

def arithToTerm [Monad M] [MonadEnv M] [Alternative M] (a : TSyntax `arith) : M <| TSyntax `term := do
  let .ok stx ← pure $ Parser.runParserCategory (← getEnv) `term (arithToString a) | failure
  return ⟨stx⟩

open IO.Process in -- code by Max Nowak from https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/external.20process/near/345090183
/-- Pipe input into stdin of the spawned process, then return output upon completion. -/
def cmdWithStdin (args : SpawnArgs) (input : String) : IO Output := do
  let child <- spawn { args with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) <- child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout <- IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr <- child.stderr.readToEnd
  let exitCode <- child.wait
  let stdout <- IO.ofExcept stdout.get
  return { exitCode, stdout, stderr }

def queryPari (s : String) : IO String := do
  let out ← cmdWithStdin { cmd := "gp", args := #["-q"]} s
  return out.stdout

elab "#symbolic" e:arith : command => do
  let out ← queryPari <| arithToString e
  logInfo out

#symbolic 2 * 3                    -- 4
#symbolic (x ^ 2 - 1) / (x + 1)    -- x - 1
#symbolic (a + 2) * (8 * a + 17)   -- 8*a^2 + 33*a + 34


elab "#pari" c:str : command => do
  let out ← queryPari c.getString
  logInfo out

#pari "nextprime(35)" -- 37

#check StdGen

elab "symb_calc" a:arith : tactic => do
  let out ← queryPari <| arithToString a
  let res ← ofExcept <| Parser.runParserCategory (← getEnv) `arith out
  let lhs : TSyntax `term ← arithToTerm a
  let rhs : TSyntax `term ← arithToTerm ⟨res⟩
  logInfo m!"{lhs} = {rhs}"
  evalTactic <| ← `(tactic| have : $lhs = $rhs := ?_; swap; try ring)

elab "symbolic#" a:arith : term => do
  let out ← queryPari <| arithToString a
  let res ← ofExcept <| Parser.runParserCategory (← getEnv) `arith out
  Term.elabTerm (← arithToTerm ⟨res⟩).raw none

variable (a : ℕ)
def x := symbolic# (a ^ 2 + 1) * (a + 2)

#print x

example (a : ℤ) : (a + 3) * (a + 5) = (a + 5) * (a + 3) := by
  symb_calc (a + 3) * (a + 5) -- (a + 3) * (a + 5) = a ^ 2 + 8 * a + 15
  rw [this]
  symb_calc (a + 5) * (a + 3) -- (a + 5) * (a + 3) = a ^ 2 + 8 * a + 15
  rw [this]

#pari "(x + 1) * (x ^2 - 1)"