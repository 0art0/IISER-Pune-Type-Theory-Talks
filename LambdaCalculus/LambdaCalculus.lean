set_option autoImplicit false

class ΛCalculus (𝓣 : Type _) where
  hom : 𝓣 → 𝓣 → 𝓣
  prod : 𝓣 → 𝓣 → 𝓣
  unit : 𝓣  

namespace ΛCalculus

local infixr:20 " ⥤ "  => hom
local infixr:32 " ⊗ " => prod 
local notation  " □ "  => unit 

structure Variable {𝓣 : Type _} [ΛCalculus 𝓣] (A : 𝓣) where
  idx : Nat
  name : String

inductive Context (𝓣 : Type _) [ΛCalculus 𝓣] where
  | nil : Context 𝓣
  | cons : {A : 𝓣} → Variable A → Context 𝓣 → Context 𝓣

local notation (priority := high) " [] " => Context.nil
local infix:50 (priority := high) " :: " => Context.cons

def Context.mem {𝓣 : Type _} [ΛCalculus 𝓣] {A : 𝓣} (v : Variable A) : Context 𝓣 → Prop
  | .nil => False
  | .cons v' ctx => (Sigma.mk A v = Sigma.mk _ v') ∨ mem v ctx

local infix:45 " ∈ " => Context.mem

def Context.subset {𝓣 : Type _} [ΛCalculus 𝓣] (Γ Γ' : Context 𝓣) :=
  ∀ {A : 𝓣} {a : Variable A}, a ∈ Γ → a ∈ Γ' 

local infix:50 " ⊆ " => Context.subset 

inductive Term {𝓣 : Type _} [ΛCalculus 𝓣] : Context 𝓣 → 𝓣 → Type _
  | var    : (Γ : Context 𝓣) → {A : 𝓣} → (v : Variable A) → Term (v :: Γ) A
  | app    : {Γ : Context 𝓣} → {A B : 𝓣} → Term Γ (A ⥤ B) → Term Γ A → Term Γ B
  | lam    : {Γ : Context 𝓣} → {A : 𝓣} → (v : Variable A) → {B : 𝓣} → Term (v :: Γ) B → Term Γ (A ⥤ B)
  | star   : {Γ : Context 𝓣} → Term Γ □
  | pair   : {Γ : Context 𝓣} → {A B : 𝓣} → Term Γ A → Term Γ B → Term Γ (A ⊗ B)
  | proj   : {Γ : Context 𝓣} → {A B : 𝓣} → Term Γ (A ⊗ B) → Term Γ A
  | proj'  : {Γ : Context 𝓣} → {A B : 𝓣} → Term Γ (A ⊗ B) → Term Γ B
  | extend : {Γ Γ' : Context 𝓣} → Γ ⊆ Γ' → {A : 𝓣} → Term Γ A → Term Γ' A

macro x:ident "⟦" n:num "⟧" : term => `(Variable.mk $n $(Lean.quote (toString x.getId)))
macro x:ident "⟦" n:num "⟧" " : " A:term : term => `((Variable.mk $n $(Lean.quote (toString x.getId)) : Variable $A))
macro "var" "⟨" v:term "⟩" : term => `(Term.var [] $v) 
local infixl:10 " ≀ " => Term.app
macro "λ " v:term " ◾ " body:term : term => `(Term.lam $v $body)
local notation " ⋆ " => Term.star
macro "⟨" x:term "," y:term "⟩" : term => `(Term.pair $x $y)
macro "π" "[" x:term "]" : term => `(Term.proj $x)
macro "π'" "[" x:term "]" : term => `(Term.proj' $x)

-- def Term.boundVariables {𝓣 : Type _} [ΛCalculus 𝓣] : {Γ : Context 𝓣} → {A : 𝓣} → Term Γ A → Context 𝓣
--   | _, _, .lam v body => v :: (boundVariables body)
--   | _, _, .app (.lam v _) body => sorry
--   | _, _, _ => []    

def Term.substitute {𝓣 : Type _} [ΛCalculus 𝓣] {Γ : Context 𝓣} {A : 𝓣} (v : Variable A) (a : Term Γ A) : Term Γ A → Term Γ A := sorry

instance : ΛCalculus Type where
  hom := fun A B ↦ (A → B)
  prod := fun A B ↦ (A × B)
  unit := Unit

example : Term [] (Nat ⥤ Nat) := λ x⟦0⟧ : Nat ◾ var⟨x⟦0⟧⟩

structure equiv {𝓣 : Type _} [ΛCalculus 𝓣] (rel : {Γ : Context 𝓣} → {A : 𝓣} → Term Γ A → Term Γ A → Prop) where
  refl   : {Γ : Context 𝓣} → {A : 𝓣} → (a : Term Γ A) → rel a a
  symm   : {Γ : Context 𝓣} → {A : 𝓣} → {a b : Term Γ A} → rel a b → rel b a
  trans  : {Γ : Context 𝓣} → {A : 𝓣} → {a b c : Term Γ A} → rel a b → rel b c → rel a c
  
  extend : {Γ Γ' : Context 𝓣} → (h : Γ ⊆ Γ') → {A : 𝓣} → {a a' : Term Γ A} → rel a a' → rel (.extend h a) (.extend h a')
  app    : {Γ : Context 𝓣} → {A B : 𝓣} → {a a' : Term Γ A} → (f : Term Γ (A ⥤ B)) → rel a a' → rel (f ≀ a) (f ≀ a')
  abst   : {Γ : Context 𝓣} → {A B : 𝓣} → (v : Variable A) → {φ φ' : Term (v :: Γ) B} → rel (λ v ◾ φ) (λ v ◾ φ')
  
  unit   : {Γ : Context 𝓣} → (a : Term Γ □) → rel a ⋆
  proj   : {Γ : Context 𝓣} → {A B : 𝓣} → {a : Term Γ A} → {b : Term Γ B} → rel π[⟨a, b⟩] a
  proj'  : {Γ : Context 𝓣} → {A B : 𝓣} → {a : Term Γ A} → {b : Term Γ B} → rel π'[⟨a, b⟩] b
  pair   : {Γ : Context 𝓣} → {A B : 𝓣} → {c : Term Γ (A ⊗ B)} → rel ⟨π[c], π'[c]⟩ c

  -- rel (.app (.lam x ϕ) a) (φ[x/a]), where `a` is substitutable in `φ`
  -- rel (.lam x (.app f (.var x))) f, if `x ∉ Γ`
  -- rel (.lam x φ) (.lam x' φ[x/x']) if `x'` is substitutable for `x` in `φ` and `x'` is not free in `φ`

end ΛCalculus