module Orn.Ornament.Examples.Maybe where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import IDesc.IDesc
open import IDesc.Fixpoint

open import IDesc.Examples.Bool

open import Orn.Ornament


-- Paper: Example 4.5

MaybeO : Set → orn BoolD id id 
MaybeO A = orn.mk (λ _ → 
           `σ (λ { zero → insert A (λ _ → `1) 
                 ; (suc zero) → `1
                 ; (suc (suc ())) }))

-- Remark: I do not delete and reintroduce the constructor names: they
-- are modelled by (anonymous) inhabitants of Fin anyway

Maybe : Set → Set
Maybe A = μ ⟦ MaybeO A ⟧orn tt

just : ∀{A} → A → Maybe A
just a = ⟨ zero , a , tt ⟩

nothing : ∀{A} → Maybe A
nothing = ⟨ suc zero , tt ⟩

-- Paper: Example 4.17
isJust : ∀{A} → Maybe A → Bool
isJust = forget
  where open import Orn.Ornament.Algebra (MaybeO _)