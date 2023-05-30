{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Numerical where

open import Ornament.TypeInType.Informed
open import Ornament.TypeInType.Orn
open import Ornament.TypeInType.OrnDesc


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
  ⊕ ⊛ : Op

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


TrieO-1  : (D : DescI Number (∅ ▷ const Type) ⊤) → OrnDesc (∅ ▷ const Type) (map₂′ (const ⊤)) (μ D (tt , ⊤) _) ! (plainDesc D)

module _ {D' : DescI Number (∅ ▷ const Type) ⊤} where
  TrieO  : (D : DescI Number (∅ ▷ const Type) ⊤) → (μ D (tt , ⊤) _ → μ D' (tt , ⊤) _) → OrnDesc (∅ ▷ const Type) (map₂′ (const ⊤)) (μ D' (tt , ⊤) _) ! (plainDesc D)
  TrieOC : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO (map₂′ (const ⊤)) W V} (C : ConI Number (∅ ▷ const Type) ⊤ V) → W ⊢ μ D' (tt , ⊤) _ → ConOrnDesc {K = μ D' (tt , ⊤) _} f ! (plainCon C)
  
  TrieO []      ix = []
  TrieO (C ∷ D) ix = TrieOC C {!!} ∷ TrieO D λ { (con n) → ix (con (inj₂ {!!})) }

  TrieOC {f = f} (𝟙 {if = if} j) ix = Δσ (λ { ((_ , A) , _) → Vec A if}) f proj₁ (𝟙 {!rough, we need to be able to construct the indices like in Nesting!} (const refl)) λ p → refl
  TrieOC (ρ {if = if} j g C) ix = {!!}
  TrieOC (σ S {if = if} h C) ix = {!!}
  TrieOC (δ {if = if} j g R h C) ix = {!!}

TrieO-1 D = TrieO {D' = D} D id
