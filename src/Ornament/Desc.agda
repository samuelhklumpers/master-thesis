{-# OPTIONS --safe #-}

module Ornament.Desc where

open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Data.Unit.Polymorphic
open import Data.Empty.Polymorphic
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J)
open import Level using (Lift)

infixl 10 _▷_
infixr 10 _∷_

private variable
  a b c : Level
  I J K : Type a
  A B C : Type a


levelOf : ∀ {a} → Type a → Level
levelOf {a} _ = a

-- telescopes
data Tel : Typeω
levelOfTel : Tel → Level
⟦_⟧tel : (Γ : Tel) → Type (levelOfTel Γ)

data Tel where
  ∅   : Tel
  _▷_ : ∀ {a} (Γ : Tel) (S : ⟦ Γ ⟧tel → Type a) → Tel

levelOfTel ∅             = ℓ-zero
levelOfTel (_▷_ {a} Γ S) = ℓ-max a (levelOfTel Γ) 

⟦ ∅     ⟧tel = ⊤
⟦ Γ ▷ S ⟧tel = Σ ⟦ Γ ⟧tel S 

private variable
  Γ Δ Θ : Tel

Cxf : (Γ Δ : Tel) → Type (ℓ-max (levelOfTel Γ) (levelOfTel Δ))
Cxf Γ Δ = ⟦ Γ ⟧tel → ⟦ Δ ⟧tel

Cxf-both : (f : Cxf Γ Δ) (S : ⟦ Δ ⟧tel → Type a) → Cxf (Γ ▷ (S ∘ f)) (Δ ▷ S)
Cxf-both f S (x , y) = f x , y



-- descriptions
-- note that we're not using Practical Generic Programming
-- you could probably always shove this layer under rec, if you cared
data Con (I : Type a) : Tel → Typeω
data Desc (I : Type a) (Γ : Tel) : Typeω where
  []  : Desc I Γ
  _∷_ : Con I Γ → Desc I Γ → Desc I Γ

levelOfCon : Con I Γ → Level
levelOfDesc : Desc I Γ → Level
levelOfDesc []      = ℓ-zero
levelOfDesc (C ∷ D) = ℓ-max (levelOfCon C) (levelOfDesc D)

data μ (D : Desc I Γ) (ps : ⟦ Γ ⟧tel) : I → Type (ℓ-max (levelOfDesc D) (levelOf I))

data Con I where
  𝟙   : (⟦ Γ ⟧tel → I) → Con I Γ

  σf  : (S : ⟦ Γ ⟧tel → Type b) → Con I (Γ ▷ S) → Con I Γ
  σf′ : (S : ⟦ Γ ⟧tel → Type b) → Con I Γ → Con I Γ
  
  σd  : (j : ⟦ Γ ⟧tel → J) (f : Cxf Γ Δ) (D : Desc J Δ) → Con I (Γ ▷ (λ x → μ D (f x) (j x))) → Con I Γ
  σd′ : (j : ⟦ Γ ⟧tel → J) (f : Cxf Γ Δ) (D : Desc J Δ) → Con I Γ → Con I Γ

  --                          v   not sure if this is ok, or if we should split parameters and values
  rec : (⟦ Γ ⟧tel → I) → (Cxf Γ Γ) → Con I Γ → Con I Γ

-- the meaningful (S : ⟦ Γ ⟧tel → Type b) → (∀ x → S x → Desc I Γ) → Desc I (Γ ▷ S)
-- should not exist! it would let constructors determine parameters

levelOfCon {I = I} (𝟙 _) = levelOf I
levelOfCon (σf  {b = b} S D) = ℓ-max b (levelOfCon D)
levelOfCon (σf′ {b = b} S D) = ℓ-max b (levelOfCon D)
levelOfCon (σd  {J = J} j f R D) = ℓ-max (levelOf J) (ℓ-max (levelOfDesc R) (levelOfCon D))
levelOfCon (σd′ {J = J} j f R D) = ℓ-max (levelOf J) (ℓ-max (levelOfDesc R) (levelOfCon D))
levelOfCon (rec i f D) = levelOfCon D

⟦_⟧Con-ℓ : (D : Con I Γ) → ∀ c
        → (⟦ Γ ⟧tel → I → Type (ℓ-max c (levelOfCon D)))
        → (⟦ Γ ⟧tel → I → Type (ℓ-max c (levelOfCon D)))
⟦ 𝟙 j                 ⟧Con-ℓ c X p i = Lift c (i ≡ (j p)) 
⟦ σf  {b = b} S     D ⟧Con-ℓ c X p i = Σ[ s ∈ S p ] ⟦ D ⟧Con-ℓ (ℓ-max b c) (X ∘ proj₁) (p , s) i 
⟦ σf′ {b = b} S     D ⟧Con-ℓ c X p i = S p × ⟦ D ⟧Con-ℓ (ℓ-max b c) X p i 
⟦ σd  {J = J} j f R D ⟧Con-ℓ c X p i = Σ[ r ∈ μ R (f p) (j p) ] ⟦ D ⟧Con-ℓ (ℓ-max c (ℓ-max (levelOf J) (levelOfDesc R))) (X ∘ proj₁) (p , r) i
⟦ σd′ {J = J} j f R D ⟧Con-ℓ c X p i = μ R (f p) (j p) × ⟦ D ⟧Con-ℓ ((ℓ-max c (ℓ-max (levelOf J) (levelOfDesc R)))) X p i
⟦ rec j f           D ⟧Con-ℓ c X p i = X (f p) (j p) × ⟦ D ⟧Con-ℓ c X p i

⟦_⟧Desc-ℓ : (D : Desc I Γ) → ∀ c → (⟦ Γ ⟧tel → I → Type (ℓ-max c (levelOfDesc D))) → ⟦ Γ ⟧tel → I → Type (ℓ-max c (levelOfDesc D))
⟦ []    ⟧Desc-ℓ c X p i = ⊥
⟦ C ∷ D ⟧Desc-ℓ c X p i = (⟦ C ⟧Con-ℓ (ℓ-max c (levelOfDesc D)) X p i) ⊎ (⟦ D ⟧Desc-ℓ (ℓ-max c (levelOfCon C)) X p i)

⟦_⟧Desc : (D : Desc I Γ) → (⟦ Γ ⟧tel → I → Type (ℓ-max (levelOf I) (levelOfDesc D))) → ⟦ Γ ⟧tel → I → Type (ℓ-max (levelOf I) (levelOfDesc D))
⟦_⟧Desc {I = I} D = ⟦ D ⟧Desc-ℓ (ℓ-max (levelOf I) (levelOfDesc D))

data μ D x where
  con : ∀ {i} → ⟦ D ⟧Desc (μ D) x i → μ D x i

