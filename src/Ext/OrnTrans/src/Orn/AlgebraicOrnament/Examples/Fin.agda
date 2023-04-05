module Orn.AlgebraicOrnament.Examples.Fin where

open import Data.Unit
open import Data.Nat hiding (_<_ ; fold)
open import Data.Fin hiding (_<_ ; fold)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import IDesc.Examples.Nat
open import IDesc.Examples.Bool

import  Orn.AlgebraicOrnament

α : Alg NatD (λ _ → Nat → Bool)
α {tt} (zero , tt) = λ _ → false
α {tt} (suc zero , f , tt) = λ { ⟨ zero , tt ⟩ → true 
                               ; ⟨ suc zero , m , tt ⟩ → f m 
                               ; ⟨ suc (suc ()) , _ ⟩ }
α {tt} (suc (suc ()) , _)

_<_ : Nat → Nat → Bool
m < n = fold NatD α n m

private
  module Test where
    test-0<0 : ze < ze ≡ false
    test-0<0 = refl

    test-1<0 : (su ze) < ze ≡ false
    test-1<0 = refl

    test-0<1 : ze < (su ze) ≡ true
    test-0<1 = refl

    test-0<2 : ze < (su (su ze)) ≡ true
    test-0<2 = refl

    test-1<1 : (su ze) < (su ze) ≡ false
    test-1<1 = refl

    test-1<2 : (su ze) < (su (su ze)) ≡ true
    test-1<2 = refl

    test-2<1 : (su (su ze)) < (su ze) ≡ false
    test-2<1 = refl

Fin' : (Nat → Bool) → Set
Fin' f = μ algOrnD (tt , f)
  where open Orn.AlgebraicOrnament.Func NatD α

{-
ize : ∀{m} → [ m ∶ m ] 
ize = ⟨ (zero , tt) , refl , tt ⟩

isu : ∀{m n} → [ m ∶ n ] → [ m ∶ su n ]
isu {m}{n} ik = ⟨ (suc zero , n , tt) , refl , ik , tt ⟩ 
-}