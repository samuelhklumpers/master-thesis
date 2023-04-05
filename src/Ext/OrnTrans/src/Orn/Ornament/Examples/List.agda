module Orn.Ornament.Examples.List where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint

open import IDesc.Examples.Nat

open import Orn.Ornament

-- Paper: Example 4.7
ListO : Set → orn NatD id id 
ListO A = mk λ _ → 
           `σ (λ { zero → `1 
                 ; (suc zero) → insert A (λ _ → `var (inv tt)) 
                 ; (suc (suc ())) })

List : Set → Set
List A = μ ⟦ ListO A ⟧orn tt

nil : ∀{A} → List A
nil = ⟨ zero , tt ⟩

cons : ∀{A} → A → List A → List A
cons a xs = ⟨ suc zero , a , xs ⟩

-- Paper: Example 4.16
length : ∀{A} → List A → Nat
length = forget
  where open import Orn.Ornament.Algebra (ListO _)
