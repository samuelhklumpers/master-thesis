{-# OPTIONS --cumulativity #-}

module HetOrn where

open import Prelude
open import ProgOrn.Ornaments
open import Cubical.Data.Bool
open import Cubical.Data.List


ListD : Type ℓ → Desc ⊤ ℓ
ListD A _ = σ Bool λ
  { false → ṿ []
  ; true  → σ[ _ ∈ A ] ṿ [ tt ] }


HetO : (F : ∀ {ℓ} → Type ℓ → Desc {ℓ = ℓ-zero} ⊤ ℓ) → ∀ {ℓ′} → OrnDesc (μ (F {ℓ = ℓ-suc ℓ′} (Type ℓ′)) tt) ! (F {ℓ = ℓ-suc ℓ′} (Type ℓ′))
HetO F {ℓ′ = ℓ′} (ok (con As)) with F {ℓ = ℓ-suc ℓ′} (Type ℓ′) tt | As
... | ṿ is  | As = go is As
  where
  go : (is : List ⊤) → Ṗ is (μ (F (Type ℓ′))) → ROrnDesc (μ (F (Type ℓ′)) tt) {ℓ-suc ℓ′} (λ _ → tt) (ṿ is)
  go []       _        = ṿ _
  go (_ ∷ is) (A , As) = ṿ (ok A , {!map!})

... | σ S D | (s , x)  = Δ {!should be s, but clearly that's not going to work!} {!!}


-- maybe this works with practical generic programming
-- or if we abstract over variables in descriptions
