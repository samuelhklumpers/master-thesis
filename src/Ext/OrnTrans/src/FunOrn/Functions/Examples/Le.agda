module FunOrn.Functions.Examples.Le where

open import Data.Unit
open import Data.Fin hiding (_<_ ; fold ; lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.Fixpoint
open import IDesc.Lifting
open import IDesc.InitialAlgebra
open import IDesc.Induction
open import IDesc.Case

open import IDesc.Examples.Nat 
open import IDesc.Examples.Bool

open import FunOrn.Functions


-- Paper: Example 5.3

type< : Type
type< = μ NatD [ tt ]→ μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤

infix 40 _<_ 

β : (Nat → Bool × ⊤) → Cases NatD (λ _ → Bool × ⊤)
β <n {i} (zero , tt) = true , tt
β <n {i} (suc zero , m) = <n m
β <n {i} (suc (suc ()) , _)


α : DAlg NatD (λ _ → Nat → Bool × ⊤)
α {i} {zero , tt}  tt = λ m → false , tt
α {i} {suc zero , n} <n = 
  case NatD (λ _ → Bool × ⊤) (λ {i} → β <n {i})
α {i} {suc (suc ()) , _} _

_<_ : ⟦ type< ⟧Type
m < n = induction NatD (λ _ → Nat → Bool × ⊤) (λ {i}{xs} → α {i}{xs}) n m

private
  module Test where

    test-m<0 : ∀{m} → m < ze ≡ false , tt
    test-m<0 = refl

    test-0<su : ∀{n} → ze < su n ≡ true , tt
    test-0<su = refl
        
    test-su<suze : ∀{m} → su m < su ze ≡ false , tt
    test-su<suze = refl

    test-suze<su : ∀{n} → su ze < su (su n) ≡ true , tt
    test-suze<su = refl


{-
pattern ze = ⟨ zero , tt ⟩
pattern su n = ⟨ suc zero , n , tt ⟩ 

_<_ : ⟦ type< ⟧Type
m < ze = false , tt
ze < su n = true , tt 
su m < su n = m < n
⟨ suc (suc ()) , _ ⟩ < _
m < ⟨ suc (suc ()) , _ ⟩
-}