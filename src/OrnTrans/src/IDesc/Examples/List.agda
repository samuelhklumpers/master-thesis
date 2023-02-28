module IDesc.Examples.List where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint

-- Paper: Example 3.6

ListD : Set → func ⊤ ⊤
ListD A = func.mk λ _ →
       `σ 2 
          (λ { zero → `1 
             ; (suc zero) → `Σ A λ _ → `var tt
             ; (suc (suc ())) })

List : Set → Set
List A = μ (ListD A) tt

nil : ∀{A} → List A
nil = ⟨ zero , tt ⟩

cons : ∀{A} → A → List A → List A
cons a xs = ⟨ suc zero , a , xs ⟩ 
