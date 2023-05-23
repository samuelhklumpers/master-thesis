{-# OPTIONS --safe #-}

module Ornament.DescL where

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
  a b c d e : Level
  I J K : Type a
  A B C : Type a


levelOf : ∀ {a} → Type a → Level
levelOf {a} _ = a

-- telescopes
data Tel : Level → Typeω
⟦_⟧tel : (Γ : Tel a) → Type a

data Tel where
  ∅   : Tel ℓ-zero
  _▷_ : (Γ : Tel a) (S : ⟦ Γ ⟧tel → Type b) → Tel (ℓ-max a b)

⟦ ∅     ⟧tel = ⊤
⟦ Γ ▷ S ⟧tel = Σ ⟦ Γ ⟧tel S 

private variable
  Γ Δ Θ : Tel a

Cxf : (Γ : Tel a) (Δ : Tel b) → Type (ℓ-max a b)
Cxf Γ Δ = ⟦ Γ ⟧tel → ⟦ Δ ⟧tel

Cxf-both : (f : Cxf Γ Δ) (S : ⟦ Δ ⟧tel → Type a) → Cxf (Γ ▷ (S ∘ f)) (Δ ▷ S)
Cxf-both f S (x , y) = f x , y

-- descriptions
-- note that we're not using Practical Generic Programming
-- you could probably always shove this layer under rec, if you cared
data Con (I : Type a) : Tel b → Level → Typeω
data Desc (I : Type a) (Γ : Tel b) : Level → Typeω where
  []  : Desc I Γ (ℓ-max a c)
  _∷_ : Con I Γ c → Desc I Γ d → Desc I Γ (ℓ-max a (ℓ-max c d))

{-
levelOfCon : Con I Γ → Level
levelOfDesc : Desc I Γ → Level
levelOfDesc []      = ℓ-zero
levelOfDesc (C ∷ D) = ℓ-max (levelOfCon C) (levelOfDesc D)
-}

data μ (D : Desc I Γ a) (ps : ⟦ Γ ⟧tel) : I → Type (ℓ-max a (levelOf I))

data Con I where
  𝟙   : (⟦ Γ ⟧tel → I) → Con I Γ (levelOf I)

  σf  : (S : ⟦ Γ ⟧tel → Type c) → Con I (Γ ▷ S) d → Con I Γ (ℓ-max c d)
  σf′ : (S : ⟦ Γ ⟧tel → Type c) → Con I Γ d → Con I Γ (ℓ-max c d)
  
  σd  : (j : ⟦ Γ ⟧tel → J) (f : Cxf Γ Δ) (D : Desc J Δ c) → Con I (Γ ▷ (λ x → μ D (f x) (j x))) d → Con I Γ (ℓ-max c (ℓ-max d (levelOf J)))
  σd′ : (j : ⟦ Γ ⟧tel → J) (f : Cxf Γ Δ) (D : Desc J Δ c) → Con I Γ d → Con I Γ (ℓ-max c (ℓ-max d (levelOf J)))

  --                          v   not sure if this is ok, or if we should split parameters and values
  rec : (⟦ Γ ⟧tel → I) → (Cxf Γ Γ) → Con I Γ c → Con I Γ c


-- the meaningful (S : ⟦ Γ ⟧tel → Type b) → (∀ x → S x → Desc I Γ) → Desc I (Γ ▷ S)
-- should not exist! it would let constructors determine parameters

{-
levelOfCon {I = I} (𝟙 _) = levelOf I
levelOfCon (σf  {b = b} S D) = ℓ-max b (levelOfCon D)
levelOfCon (σf′ {b = b} S D) = ℓ-max b (levelOfCon D)
levelOfCon (σd  {J = J} j f R D) = ℓ-max (levelOf J) (ℓ-max (levelOfDesc R) (levelOfCon D))
levelOfCon (σd′ {J = J} j f R D) = ℓ-max (levelOf J) (ℓ-max (levelOfDesc R) (levelOfCon D))
levelOfCon (rec i f D) = levelOfCon D
-}

⟦_⟧Con-ℓ : (D : Con I Γ a) → ∀ b → (⟦ Γ ⟧tel → I → Type (ℓ-max a b)) → (⟦ Γ ⟧tel → I → Type (ℓ-max a b))
⟦ 𝟙 j         ⟧Con-ℓ b X p i = Lift b (i ≡ (j p)) 
⟦ σf  {c = c} S     D ⟧Con-ℓ b X p i = Σ[ s ∈ S p ] ⟦ D ⟧Con-ℓ (ℓ-max b c) (X ∘ proj₁) (p , s) i 
⟦ σf′ {c = c} S     D ⟧Con-ℓ b X p i = S p × ⟦ D ⟧Con-ℓ (ℓ-max b c) X p i 
⟦ σd  {J = J} {c = c} j f R D ⟧Con-ℓ b X p i = Σ[ r ∈ μ R (f p) (j p) ] ⟦ D ⟧Con-ℓ (ℓ-max b (ℓ-max c (levelOf J))) (X ∘ proj₁) (p , r) i
⟦ σd′ {J = J} {c = c} j f R D ⟧Con-ℓ b X p i = μ R (f p) (j p) × ⟦ D ⟧Con-ℓ (ℓ-max b (ℓ-max c (levelOf J))) X p i
⟦ rec j f   D ⟧Con-ℓ b X p i = X (f p) (j p) × ⟦ D ⟧Con-ℓ b X p i

⟦_⟧Desc-ℓ : (D : Desc I Γ a) → ∀ c → (⟦ Γ ⟧tel → I → Type (ℓ-max c a)) → ⟦ Γ ⟧tel → I → Type (ℓ-max c a)
⟦_⟧Desc-ℓ [] c X p i = ⊥
⟦_⟧Desc-ℓ {I = I} (_∷_ {c = a} {d = d} C D) c X p i = (⟦ C ⟧Con-ℓ (ℓ-max c (ℓ-max d (levelOf I))) X p i) ⊎ (⟦ D ⟧Desc-ℓ (ℓ-max c (ℓ-max a (levelOf I))) X p i)

⟦_⟧Desc : (D : Desc I Γ a) → (⟦ Γ ⟧tel → I → Type (ℓ-max (levelOf I) a)) → ⟦ Γ ⟧tel → I → Type (ℓ-max (levelOf I) a)
⟦_⟧Desc {I = I} D = ⟦ D ⟧Desc-ℓ (levelOf I)

data μ D x where
  con : ∀ {i} → ⟦ D ⟧Desc (μ D) x i → μ D x i

