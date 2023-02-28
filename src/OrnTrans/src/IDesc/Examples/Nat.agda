module IDesc.Examples.Nat where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint


-- Paper: Example 3.6

NatD : func ⊤ ⊤
NatD = mk λ _ →
       `σ 2 
          (λ { zero → `1 
             ; (suc zero) → `var tt
             ; (suc (suc ())) }) 

Nat : Set
Nat = μ NatD tt

ze : Nat
ze = ⟨ zero , tt ⟩

su : Nat → Nat
su n = ⟨ suc zero , n ⟩ 

private
  module Test where
    test-ze : Nat
    test-ze = ze

    test-su : Nat → Nat
    test-su n = su n
