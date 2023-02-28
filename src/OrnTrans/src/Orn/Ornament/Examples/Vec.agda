module Orn.Ornament.Examples.Vec where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic


open import IDesc.IDesc
open import IDesc.Fixpoint


open import Orn.Ornament

u : ℕ → ⊤
u _ = tt

ListD : Set → func ⊤ ⊤
ListD A = func.mk λ _ → `Σ (Fin 2) (λ { zero → `1 
                                      ; (suc zero) → `Σ A λ _ → `var tt 
                                      ; (suc (suc ())) })

module Constraint {A : Set} where

  VecO : orn (ListD A) u u
  VecO = orn.mk λ n → 
         `Σ {S = Fin 2}
             λ { zero → insert (0 ≡ n) λ _ → 
                        `1
               ; (suc zero) → insert ℕ λ m → 
                              insert (suc m ≡ n) λ _ → 
                              `Σ λ _ →
                              `var (inv m) 
               ; (suc (suc ())) }

  Vec : ℕ → Set
  Vec = μ ⟦ VecO ⟧orn 
  
  nil : Vec 0
  nil = ⟨ zero , refl , tt ⟩
  
  cons : ∀{n} → A → Vec n → Vec (suc n)
  cons {n} a xs = ⟨ suc zero , n , refl , a , xs  ⟩

module Compute {A : Set} where

  VecO : orn (ListD A) u u
  VecO = orn.mk λ { zero → insert (Fin 1) λ { zero → deleteΣ zero `1
                                            ; (suc ()) }
                  ; (suc n) → insert (Fin 1) λ { zero → deleteΣ (suc zero) (`Σ λ _ → `var (inv n)) 
                                               ; (suc ()) } }

  Vec : ℕ → Set
  Vec = μ ⟦ VecO ⟧orn 
  
  nil : Vec 0
  nil = ⟨ zero , tt ⟩

  cons : ∀{n} → A → Vec n → Vec (suc n)
  cons a xs = ⟨ zero , a , xs ⟩
