module Orn.AlgebraicOrnament.Examples.Leq where

open import Logic.IProp

open import Data.Unit
open import Data.Nat hiding (_+_ ; fold)
open import Data.Fin hiding (lift ; _+_ ; fold)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import IDesc.Examples.Nat

import  Orn.AlgebraicOrnament
import  Orn.AlgebraicOrnament.Coherence

-- Paper: Example 4.23

α+m : Nat → Alg NatD (λ _ → Nat)
α+m m {tt} (zero , tt) = m
α+m m {tt} (suc zero , n) = su n
α+m m {tt} (suc (suc ()) , _)

_+_ : Nat → Nat → Nat
m + n = fold NatD (α+m m) n

_≦_ : Nat → Nat → Set
m ≦ n = μ algOrnD (tt , n)
  where open Orn.AlgebraicOrnament.Func NatD (α+m m)

ize : ∀{m} → m ≦ m 
ize = ⟨ (zero , tt) , refl , tt ⟩

isu : ∀{m n} → m ≦ n → m ≦ su n
isu {m}{n} ik = ⟨ (suc zero , n) , refl , ik ⟩ 

forgetOrnament : ∀{m n} → m ≦ n → Nat
forgetOrnament {m} = forgetAlgOrn
    where open Orn.AlgebraicOrnament.Coherence NatD (α+m m)

lemma-coherence : ∀ {m n} → (t : m ≦ n) → ⊢ n ≡ m + forgetOrnament t
lemma-coherence {m} = coherentOrn 
  where open Orn.AlgebraicOrnament.Coherence NatD (α+m m)
