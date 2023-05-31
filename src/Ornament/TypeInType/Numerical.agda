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

{- data Op : Type where
  ⊕ ⊛ : Op -}

Op = ℕ
  

Number : Info
Number .𝟙i = ℕ
Number .ρi = Op
Number .σi S = ∀ p → S p → ℕ
Number .δi Γ J = Γ ≡ ∅ × J ≡ ⊤ × Op

NatND : DescI Number ∅ ⊤
NatND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 1} _ (𝟙 {if = 1} _)
      ∷ []

BinND : DescI Number ∅ ⊤
BinND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 2} _ (𝟙 {if = 1} _)
      ∷ ρ0 {if = 2} _ (𝟙 {if = 2} _)
      ∷ []

DigND : DescI Number ∅ ⊤
DigND = 𝟙 {if = 1} _
      ∷ 𝟙 {if = 2} _
      ∷ 𝟙 {if = 3} _
      ∷ []

FingND : DescI Number (∅ ▷ const Type) ⊤
FingND = 𝟙 {if = 0} _
       ∷ 𝟙 {if = 1} _
       ∷ δ- {if = refl , refl , 1} _ _ DigND (ρ0 {if = 1} _ (δ- {if = refl , refl , 1} _ _ DigND (𝟙 {if = 0} _)))
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

-- C = ρ _ g C′ then C2 = ρ j h C′2
-- μ (C2 A (r , n)) = ⟦ ρ j g C′2 ⟧ (μ C2) A (r , n)
--                  = μ C2 (g A) (j r) × ⟦ C′2 ⟧ (μ C2) A n ≃ Vec A ???
--                  = Vec A (g (toℕ (j r)) + n)                                        


-- so full ρ in numbers does not work, or maybe in a very restricted sense (you would need ρi to be something like Op × ((g : Cxf Γ Γ) → map g ℕ → ℕ) 
-- ρ0 should work, so define RegDesc < Desc and RegCon < Con

-- on the other hand, σi could be used for variable multiplication?
-- let's keep it as just a variable + for now

-- similarly δ breaks a bit because all of the sudden numbers can sneak parameters back in
-- can we use Info to enforce constraints on the components? (actually, probably yes)

{-# TERMINATING #-}
TrieO-1  : (D : DescI Number ∅ ⊤) → OrnDesc (∅ ▷ const Type) ! (μ D tt _) ! (plainDesc D)

module _ {D' : DescI Number ∅ ⊤} where
  TrieO  : (D : DescI Number ∅ ⊤) → (⟦ D ⟧ (μ D') tt _ → μ D' tt _) → OrnDesc (∅ ▷ const Type) ! (μ D' tt _) ! (plainDesc D)
  TrieOC : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! W V} (C : ConI Number ∅ ⊤ V) → (∀ {p} w → ⟦ C ⟧ (μ D') (tt , f {p = p} w) _ → μ D' tt _) → ConOrnDesc {K = μ D' tt _} f ! (plainCon C)
  
  TrieO []      ix = []
  TrieO (C ∷ D) ix = TrieOC C (λ v x → ix (inj₁ x)) ∷ TrieO D (ix ∘ inj₂)

  TrieOC {f = f} (𝟙 {if = if} j) ix =                               -- if the number is constantly if here
    Δσ (λ { ((_ , A) , _) → Vec A if}) f proj₁                      -- add if A's here
    (𝟙 (λ { ((_ , A) , w) → ix w refl })                            -- the index is completely determined by the context
    (const refl)) λ p → refl  
    
  TrieOC {f = f} (ρ {if = if} j g C) ix =                           -- if the number is recursively if * r + n here
    Δσ (const (μ D' tt tt)) (f ∘ proj₁) id                          -- for an index r
    (ρ (proj₂ ∘ proj₂) (λ { (_ , A) → _ , Vec A if })               -- keep the recursive field at r with parameter A^k
    (TrieOC C λ { (w , r) n → ix w (r , n) } )                      -- and compute the rest of the OD, the index is constructed from r and the context
    (λ p → refl) λ p → refl) λ p → refl
    
  TrieOC {f = f} (σ S {if = if} h C) ix =
    σ S id (h ∘ VxfO-▷ f S)
    (Δσ (λ { ((_ , A) , _ , s) → Vec A (if _ s) }) (h ∘ _) id
    (TrieOC C λ { ((w , s) , x) n → ix w (s , n) })
    λ p → refl) (λ p → refl)

  TrieOC {f = f} (δ {if = Δ≡∅ , J≡⊤ , if} j g R h C) ix =
    Δσ (const (μ D' tt tt)) (f ∘ proj₁) id
    (∙δ {!!} {!!} {!!} {!!} {!!} {!!} {!!}
    (TrieO-1 (subst2 (DescI Number) Δ≡∅ J≡⊤ R)))
    λ p → refl

TrieO-1 D = TrieO {D' = D} D con
