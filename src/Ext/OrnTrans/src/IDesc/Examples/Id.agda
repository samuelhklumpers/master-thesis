module IDesc.Examples.Id {A : Set} where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint


-- Paper: Remark 3.11
IdD : A → func A A
IdD a₁ = func.mk λ a₂ → 
         `Σ (Fin 1) λ 
          { zero → `Σ (a₁ ≡ a₂) λ _ → `1 
          ; (suc ()) }

Id : A → A → Set
Id a₁ a₂ = μ (IdD a₁) a₂



