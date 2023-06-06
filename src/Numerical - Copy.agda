{-# OPTIONS --type-in-type --with-K #-}


module Ornament.Numerical where

open import Ornament.Informed
open import Ornament.Orn
open import Ornament.OrnDesc


open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base
open import Data.Vec using (Vec)

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude using (cong; sym; refl; _∙_; subst; subst2)



private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ


open Info

data Op : Type where
  ⊕ : Op

Number : Info
Number .𝟙i = ℕ
Number .ρi = Op
Number .σi S = Op × ∀ p → S p → ℕ
Number .δi = Op

NatND : DescI Number ∅ ⊤
NatND = 𝟙 {if = 0} _
      ∷ ρ0 {if = ⊕} _ (𝟙 {if = 1} _)
      ∷ []

BinND : DescI Number ∅ ⊤
BinND = 𝟙 {if = 0} _
      ∷ σ- (const ⊤) {if = ⊕ , λ _ _ → 1} (ρ0 {if = ⊛} _ (𝟙 {if = 2} _))
      ∷ σ- (const ⊤) {if = ⊕ , λ _ _ → 1} (ρ0 {if = ⊛} _ (𝟙 {if = 2} _))
      ∷ []

DigND : DescI Number ∅ ⊤
DigND = 𝟙 {if = 1} _
      ∷ 𝟙 {if = 2} _
      ∷ 𝟙 {if = 3} _
      ∷ []

FingND : DescI Number (∅ ▷ const Type) ⊤
FingND = 𝟙 {if = 0} _
       ∷ 𝟙 {if = 1} _
       ∷ δ- {if = ⊕} _ _ DigND (ρ0 {if = ⊕} _ (δ- {if = ⊕} _ _ DigND (𝟙 {if = 0} _)))
       ∷ []

-- goal : D2 = toDesc (TrieO-1 D) ⇒ μ (D2 A n) ≃ Vec A (toℕ n)
-- if D = C ∷ D′, then D2 = C2 ∷ D′2 and we need
-- μ (D2 A (inj₁ n)) = ⟦ C2 ⟧  (μ D2) A n ≃ Vec A (toℕ n)
-- μ (D2 A (inj₂ n)) = ⟦ D′2 ⟧ (μ D2) A n ≃ Vec A (toℕ n)

-- C = ρ0 _ C′ then C2 = ρ j g C′2
-- μ (C2 A (r , n)) = ⟦ ρ j g C′2 ⟧ (μ C2) A (r , n)
--                  = μ C2 (g A) (j r) × ⟦ C′2 ⟧ (μ C2) A n ≃ Vec A (toℕ (r , n))
--                  = Vec A (g (toℕ (j r)) + n)                                                     
-- toℕ {if = ⊕} (r , n) = toℕ r + toℕ n
-- toℕ {if = ⊛} (r , n) = toℕ r * toℕ n

-- ⇒ this is only going to work if ⊛ is not *
-- let's just settle for toℕ {if = ⊛ k} (r , n) = k * r + n
-- i.e. Op = ℕ

TrieO-1  : (D : DescI Number (∅ ▷ const Type) ⊤) → OrnDesc (∅ ▷ const Type) (map₂′ (const ⊤)) (μ D (tt , ⊤) _) ! (plainDesc D)

module _ {D' : DescI Number (∅ ▷ const Type) ⊤} where
  TrieO  : (D : DescI Number (∅ ▷ const Type) ⊤) → (μ D (tt , ⊤) _ → μ D' (tt , ⊤) _) → OrnDesc (∅ ▷ const Type) (map₂′ (const ⊤)) (μ D' (tt , ⊤) _) ! (plainDesc D)
  TrieOC : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO (map₂′ (const ⊤)) W V} (C : ConI Number (∅ ▷ const Type) ⊤ V) → W ⊢ μ D' (tt , ⊤) _ → ConOrnDesc {K = μ D' (tt , ⊤) _} f ! (plainCon C)
  
  TrieO []      ix = []
  TrieO (C ∷ D) ix = TrieOC C {!!} ∷ TrieO D λ { (con n) → ix (con (inj₂ {!!})) }

  TrieOC {f = f} (𝟙 {if = if} j) ix = Δσ (λ { ((_ , A) , _) → Vec A if}) f proj₁ (𝟙 {!!} (const refl)) λ p → refl
  TrieOC (ρ {if = if} j g C) ix = {!!}
  TrieOC (σ S {if = if} h C) ix = {!!}
  TrieOC (δ {if = if} j g R h C) ix = {!!}

TrieO-1 D = TrieO {D' = D} D id
