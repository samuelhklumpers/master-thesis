module FunOrn.Functions.Examples.Plus where


open import Data.Unit
open import Data.Fin hiding (_+_ ; lift)
open import Data.Product

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Induction
open import IDesc.Examples.Nat hiding (ze ; su)

open import FunOrn.Functions

-- Paper: Example 5.4

type+ : Type
type+ = μ NatD [ tt ]→ μ NatD [ tt ]→ μ NatD [ tt ]× `⊤

infix 40 _+_ 

pattern ze = ⟨ zero , tt ⟩
pattern su n = ⟨ suc zero , n ⟩ 

_+'_ : ⟦ type+ ⟧Type
m +' ze = m , tt
m +' su n = su (proj₁ (m +' n)) , tt 
m +' ⟨ suc (suc ()) , _ ⟩


α : Nat → DAlg NatD (λ _ → Nat × ⊤)
α m {tt} {zero , tt} tt = m , tt
α m {tt} {suc zero , n } (m+n , tt) = su m+n , tt
α m {tt} {suc (suc ()) , _} _

_+_ : ⟦ type+ ⟧Type
m + n = induction NatD (λ _ → Nat × ⊤) (λ {i}{xs} → α m {i}{xs}) n

private
  module Test where

    open import Relation.Binary.PropositionalEquality

    test-0+0 : ze + ze ≡ ze +' ze
    test-0+0 = refl
  
    test-m+0 : ∀{m} → m + ze ≡ (m , tt)
    test-m+0 = refl

    test-m+1 : ∀{m} → m + (su ze) ≡ m +' (su ze)
    test-m+1 = refl

    test-m+2 : ∀{m} → m + (su (su ze)) ≡ m +' (su (su ze))
    test-m+2 = refl
