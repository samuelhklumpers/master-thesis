module Orn.Brady.Vec 
         (A : Set)
       where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.Fixpoint
open import IDesc.Examples.Vec

open import Orn.Ornament

-- Paper: Example 4.10

VecO : orn (Constraint.VecD A) id id
VecO = orn.mk λ { zero → insert (Fin 1) λ { zero → deleteΣ zero (deleteΣ refl `1) 
                                          ; (suc ()) } 
                ; (suc n) → insert (Fin 1) λ { zero → deleteΣ (suc zero) 
                                                     (deleteΣ n 
                                                     (deleteΣ refl 
                                                     (`Σ (λ _ → 
                                                      `var (inv n)))))
                                             ; (suc ()) } }

Vec : ℕ → Set
Vec = μ ⟦ VecO ⟧orn 
  
nil : Vec 0
nil = ⟨ zero , tt ⟩

cons : ∀{n} → A → Vec n → Vec (suc n)
cons a xs = ⟨ zero , a , xs ⟩
