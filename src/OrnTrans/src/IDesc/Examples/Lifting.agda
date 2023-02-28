module IDesc.Examples.Lifting where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Vec renaming (Vec to VecNative)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged

module Compute where
  
  VecD : (A : Set) → func ℕ ℕ
  VecD A = func.mk (λ { zero → `1 
                      ; (suc n) → `Σ A λ _ → `var n `× `1 })

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (VecD A)

  nil : ∀{A} → Vec A 0
  nil = ⟨ tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ a , xs , tt ⟩

module Constraint where

  VecD : (A : Set) → func ℕ ℕ
  VecD A = func.mk (λ n → `Σ (Fin 2) 
                          λ { zero → `Σ (n ≡ 0) λ _ → `1  
                            ; (suc zero) → `Σ A λ _ → 
                                           `Σ ℕ λ m → 
                                           `Σ (n ≡ suc m) λ _ → 
                                           `var m `× `1
                            ; (suc (suc ())) } )

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (VecD A)

  nil : ∀{A} → Vec A 0
  nil = ⟨ zero , refl , tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ suc zero , a , _ , refl , xs , tt ⟩

module TaggedCompute where

  VecD : (A : Set) → tagDesc ℕ
  VecD A = (0 , λ n → []) ,
           (λ { zero → 1 
              ; (suc n) → 1 }) ,
           (λ { zero → `1 ∷ [] 
              ; (suc n) → (`Σ A λ _ → `var n `× `1) ∷ [] })

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (toDesc (VecD A))

  nil : ∀{A} → Vec A 0
  nil = ⟨ zero , tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ zero , a , xs , tt ⟩

module TaggedConstraint where

  VecD : (A : Set) → tagDesc ℕ
  VecD A = (2 , λ n → 
              (`Σ (n ≡ 0) λ _ → `1) ∷ 
              (`Σ A λ _ → 
               `Σ ℕ λ m → 
               `Σ (n ≡ suc m) λ _ → 
               `var m `× `1) ∷ []) ,
           ((λ n → 0) , λ n → [])

  Vec : (A : Set) → ℕ → Set
  Vec A = μ (toDesc (VecD A))

  nil : ∀{A} → Vec A 0
  nil = ⟨ zero , refl , tt ⟩

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons a xs = ⟨ suc zero , a , _ , refl , xs , tt ⟩