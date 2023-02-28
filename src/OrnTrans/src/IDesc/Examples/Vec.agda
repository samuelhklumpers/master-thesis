module IDesc.Examples.Vec where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Vec renaming (Vec to VecNative)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged

-- Paper: Example 3.7

module Constraint where

  VecD : (A : Set) → func ℕ ℕ
  VecD A = func.mk (λ n → `Σ (Fin 2) 
                          λ { zero → `Σ (n ≡ 0) λ _ → `1  
                            ; (suc zero) → `Σ ℕ λ m → 
                                           `Σ (n ≡ suc m) λ _ → 
                                           `Σ A λ _ → 
                                           `var m 
                            ; (suc (suc ())) } )

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (VecD A)

  nil : ∀{A} → Vec A 0
  nil = ⟨ zero , refl , tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ suc zero ,  _ , refl , a , xs  ⟩

-- Paper: Example 3.8

module Compute where
  
  VecD : (A : Set) → func ℕ ℕ
  VecD A = func.mk (λ { zero → `Σ (Fin 1) λ { zero → `1 
                                            ; (suc ()) } 
                      ; (suc n) → `Σ (Fin 1) λ { zero → `Σ A λ _ → `var n `× `1 
                                               ; (suc ()) }})

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (VecD A)

  nil : ∀{A} → Vec A 0
  nil = ⟨ zero , tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ zero , a , xs , tt ⟩

