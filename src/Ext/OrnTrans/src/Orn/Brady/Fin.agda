module Orn.Brady.Fin where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift) renaming (zero to zeF ; suc to suF)
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.Fixpoint
open import IDesc.Examples.Fin

open import Orn.Ornament

-- Paper: Example 4.11

FinO : orn Constraint.FinD id id
FinO = orn.mk λ { zero → insert ⊥ λ ()
                ; (suc n) → `Σ (λ { zeF → deleteΣ n (deleteΣ refl `1) 
                                  ; (suF zeF) → deleteΣ n (deleteΣ refl (`var (inv n))) 
                                  ; (suF (suF ())) }) } 

Fin' : ℕ → Set
Fin' = μ ⟦ FinO ⟧orn 
  
fz : ∀{n} → Fin' (suc n)
fz {n} = ⟨ zeF , tt ⟩
  
fs : ∀{n} → Fin' n → Fin' (suc n)
fs {n} k = ⟨ suF zeF , k ⟩

-- Paper: Example 4.19
forgetFin : ∀{n} → Fin' n → Constraint.Fin n
forgetFin = forget
  where open import Orn.Ornament.Algebra FinO
