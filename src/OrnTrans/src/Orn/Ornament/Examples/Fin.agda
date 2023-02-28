module Orn.Ornament.Examples.Fin where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift) renaming (zero to zeF ; suc to suF )
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint

open import IDesc.Examples.Nat

open import Orn.Ornament

u : ℕ → ⊤
u _ = tt

module Constraint where

  -- Paper: Example 4.8

  FinO : orn NatD u u
  FinO = mk λ n → 
         `σ (λ { zeF → insert ℕ λ m →
                        insert (suc m ≡ n) λ _ → 
                        `1
               ; (suF zeF) → insert ℕ λ m → 
                              insert (suc m ≡ n) λ _ → 
                              `var (inv m) 
               ; (suF (suF ())) })

  

  FinO' : orn NatD u u
  FinO' = mk λ n → `σ (λ { zeF → {!!} ; (suF zeF) → ? })

  Fin' : ℕ → Set
  Fin' = μ ⟦ FinO ⟧orn 
  
  fz : ∀{n} → Fin' (suc n)
  fz {n} = ⟨ zeF , n , refl , tt ⟩
  
  fs : ∀{n} → Fin' n → Fin' (suc n)
  fs {n} k = ⟨ suF zeF , n , refl , k ⟩

  -- Paper: Example 4.18
  forgetFin : ∀{n} → Fin' n → Nat
  forgetFin = forget
    where open import Orn.Ornament.Algebra FinO

module Compute where

  FinO : orn NatD u u
  FinO = mk λ { zero → insert ⊥ ⊥-elim
                  ; (suc n) → 
                    `σ λ { zeF → `1
                  ; (suF zeF) → `var (inv n) 
                  ; (suF (suF ())) } }

  Fin' : ℕ → Set
  Fin' = μ ⟦ FinO ⟧orn 
  
  fz : ∀{n} → Fin' (suc n)
  fz {n} = ⟨ zeF , tt ⟩
  
  fs : ∀{n} → Fin' n → Fin' (suc n)
  fs {n} k = ⟨ suF zeF , k ⟩
