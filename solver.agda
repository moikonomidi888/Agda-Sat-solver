module verified_solver where

open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ; Σ-syntax)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _^_)
open import Data.List.Base using (length)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Syntax and Semantics
------------------------------------------------------------------------

data Formula : Set where
  AND : Formula → Formula → Formula
  OR  : Formula → Formula → Formula
  NOT : Formula → Formula
  VAR : ℕ → Formula

data VBool : Set where
  VR : ℕ → VBool   -- “Undecided”: the variable is not yet assigned.
  T  : VBool       -- True
  F  : VBool       -- False

_+++_ : VBool → VBool → VBool
VR x +++ VR y = VR x
T    +++ b   = b
b    +++ F   = F
b    +++ T   = b
F    +++ b   = F

_//_ : VBool → VBool → VBool
VR x // VR y = VR x
T    // b   = T
b    // T   = T
F    // b   = b
b    // F   = b

neg : VBool → VBool
neg (VR x) = VR x
neg T      = F
neg F      = T

------------------------------------------------------------------------
-- 2. Environment and Evaluation
------------------------------------------------------------------------

-- An environment is a list of assignments (variable, Bool)
Environment : Set
Environment = List (ℕ × Bool)

-- In our solver we keep an extended assignment (a list of pairs paired with a decision flag).
-- A flag of false indicates that the decision is still “open” (has not been flipped yet).
-- The function `extr` drops these flags.
extr : List ((ℕ × Bool) × Bool) → Environment
extr [] = []
extr (((x , b) , _) ∷ xs) = (x , b) ∷ extr xs

-- A lookup function in an environment.
lookup : ℕ → Environment → Maybe Bool
lookup x [] = nothing
lookup x ((y , b) ∷ ys) with x ≟ y
... | yes _ = just b
... | no _  = lookup x ys

-- The evaluation function. If a variable is unassigned (lookup fails),
-- we return the “undecided” value VR x.
eval : Formula → Environment → VBool
eval (VAR x) env with lookup x env
... | nothing    = VR x
... | just true  = T
... | just false = F
eval (AND φ ψ) env = eval φ env +++ eval ψ env
eval (OR φ ψ)  env = eval φ env // eval ψ env
eval (NOT φ)   env = neg (eval φ env)

------------------------------------------------------------------------
-- 3. Backtracking and the Terminating Solver
------------------------------------------------------------------------

-- Backtracking: search the extended assignment list for the most recent decision
-- that has not yet been flipped. When found, flip that decision.
backtr : List ((ℕ × Bool) × Bool) → Maybe (List ((ℕ × Bool) × Bool))
backtr [] = nothing
backtr (((x , b) , decision) ∷ xs) with decision
... | false = just (((x , not b) , true) ∷ xs)
... | true  = backtr xs

mutual
  -- Main solver.
  --   solve : ℕ → (extended assignment) → Formula → Maybe Environment
  -- The fuel argument (of type ℕ) decreases on every recursive call.
  solve : ℕ → List ((ℕ × Bool) × Bool) → Formula → Maybe Environment
  solve zero _ _ = nothing
  solve (suc fuel) x phi = solve-aux (eval phi (extr x)) fuel x phi

  -- Auxiliary function that pattern–matches on the evaluation result.
  solve-aux : VBool → ℕ → List ((ℕ × Bool) × Bool) → Formula → Maybe Environment
  solve-aux T      fuel x phi = just (extr x)
  solve-aux F      fuel x phi with backtr x
  ... | just y  = solve fuel y phi
  ... | nothing = nothing
  solve-aux (VR y) fuel x phi = solve fuel (((y , true) , false) ∷ x) phi

------------------------------------------------------------------------
-- 4. A Fuel Bound Based on the Variables in the Formula
------------------------------------------------------------------------

vars : Formula → List ℕ
vars (VAR x)   = x ∷ []
vars (AND φ ψ) = vars φ ++ vars ψ
vars (OR φ ψ)  = vars φ ++ vars ψ
vars (NOT φ)   = vars φ

fuelBound : Formula → ℕ
fuelBound phi = 2 ^ (length (vars phi))
