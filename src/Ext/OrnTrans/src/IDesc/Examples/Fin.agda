module IDesc.Examples.Fin where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift) renaming (Fin to FinNative)
open import Data.Vec 
open import Data.Empty
open import Data.Product
open import Data.Fin renaming (Fin to FinA)

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged

-- Paper: Example 3.7
module Constraint where

  FinD : func ℕ ℕ
  FinD = func.mk λ n →
          `Σ (FinA 2) λ
             { zero → `Σ ℕ λ n' → 
                      `Σ (n ≡ suc n') λ _ → 
                      `1
             ; (suc zero) → `Σ ℕ λ n' →
                            `Σ (n ≡ suc n') λ _ →
                            `var n'
             ; (suc (suc ())) }

  Fin : ℕ → Set
  Fin = μ FinD

  ze : ∀{n} → Fin (suc n)
  ze = ⟨ zero , _ , refl , tt ⟩

  su : ∀{n} → Fin n → Fin (suc n)
  su k = ⟨ suc zero , _ , refl , k ⟩ 


-- Paper: Example 3.8
module Compute where

  FinD : func ℕ ℕ
  FinD = func.mk λ 
         { zero → `Σ ⊥ λ () 
         ; (suc n) → `Σ (FinA 2) λ 
                        { zero → `1 
                        ; (suc zero) → `var n 
                        ; (suc (suc ())) } }

  Fin : ℕ → Set
  Fin = μ FinD

  ze : ∀{n} → Fin (suc n)
  ze = ⟨ zero , tt ⟩

  su : ∀{n} → Fin n → Fin (suc n)
  su k = ⟨ suc zero , k ⟩ 

