module IDesc.Examples.Ordinal where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint

-- Paper: Example 3.6

OrdD : func ⊤ ⊤
OrdD = func.mk λ _ →
       `σ 3
          (λ { zero → `1 
             ; (suc zero) → `var tt
             ; (suc (suc zero)) → `Π ℕ λ _ → `var tt
             ; (suc (suc (suc ()))) })

Ord : Set
Ord = μ OrdD tt

ze : Ord
ze = ⟨ zero , tt ⟩

su : Ord → Ord
su n = ⟨ suc zero , n ⟩ 

lim : (ℕ → Ord) → Ord
lim f = ⟨ suc (suc zero) , f ⟩ 
