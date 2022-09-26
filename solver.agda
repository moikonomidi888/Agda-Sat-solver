module solver where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
open import Data.Bool renaming (not to ¬♭_; _∨_ to _∨♭_; _∧_ to _∧♭_)
open import Data.Vec using (Vec; _∷_; []; [_]; lookup)
open import Data.Nat
open import Data.Maybe
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Data.Product
open import Data.List.Base
open import Function.Base using (case_of_; case_return_of_)
open import Data.List.Base
open import Data.Bool.Base using (not)
open import Data.Product using (_×_; ∃; ∃-syntax)
open import Data.Fin



infixl 4 _∨_
infixl 4 _∧_
infixl 6 ¬_

data Formula : (n : ℕ) → Set where
 var_     : {m : ℕ}  → (n : Fin m) → Formula m
 ¬_        : {m : ℕ} → Formula m → Formula m
 _∨_      : {m : ℕ} → Formula m → Formula m → Formula m
 _∧_      : {m : ℕ} → Formula m → Formula m → Formula m

data VBool : (n : ℕ) → Set where
   VR       : {m : ℕ} → (n : Fin m) -> VBool m
   VT       : {m : ℕ} →  VBool m
   VF       : {m : ℕ} →  VBool m

_+++_         : {m : ℕ} → VBool m → VBool m → VBool m
(VR m) +++ (VR y)   = VR m
VT +++ b            =  b
b +++ VF            =  VF
b +++ VT            =  b
VF +++ b            =  VF


_//_         :  {m : ℕ} →  VBool m → VBool m → VBool m
VR x // VR y  = VR x
VT // b       = VT
b // VT       = VT
VF // b       = b
b // VF       = b

neg        :  {m : ℕ} → VBool m → VBool m
neg (VR x)  = VR x
neg VT      =  VF
neg VF      =  VT

transformVBool      : {m : ℕ} →  Bool -> VBool m
transformVBool true = VT
transformVBool false = VF

searchFor     : {m : ℕ} → Fin m → List (Fin m × Bool) -> VBool m
searchFor a [] = VR a
searchFor a (y ∷ ys) = case (toℕ a ≡ᵇ toℕ (proj₁ y)) of λ
                    {  true  -> (transformVBool(proj₂ y));
                      false  -> (searchFor a ys)
                      }

extr               : {m : ℕ} → List ((Fin m × Bool) × Bool) -> List (Fin m × Bool)
extr  (x ∷ xs) =  ((proj₁ x) ∷ extr xs)
extr []                    = []

eval               : {m : ℕ} → Formula m → List (Fin m × Bool) → VBool m
eval  (var b) y    = searchFor b y
eval (x ∧ y) j    = eval x j +++ eval y j
eval (x ∨ y) j    = eval x j // eval y j
eval (¬ x) y      = neg (eval x y)

backtr              :{m : ℕ} →  List ((Fin m × Bool) × Bool) → Maybe (List ((Fin m × Bool) × Bool))
backtr (((n , b) , false) ∷ xs) = (just (((n , (not b)) , true) ∷ xs))
backtr (((x , b) , true) ∷ xs)  = backtr xs
backtr  []                      = nothing

{-# NON_TERMINATING #-}

auxSolve  :{m : ℕ} → List ((Fin  m × Bool) × Bool) -> Formula m -> Maybe (List (Fin m × Bool))
auxSolve x phi = case (eval phi (extr x)) of λ
                     {(VR n)     ->  auxSolve(((n , true) , false) ∷ x) phi;
                     VT          ->  just (extr x);
                     VF          ->  case backtr x of λ
                       {(just n) -> auxSolve n phi;
                        nothing  -> nothing
                        }
                       }
                       
solve :{m : ℕ} →  Formula m → Maybe (List (Fin m × Bool))
solve z = auxSolve [] z
