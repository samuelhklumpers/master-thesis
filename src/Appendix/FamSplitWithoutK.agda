{-# OPTIONS --without-K #-}

data ⊤ : Set where
  tt : ⊤

data ℕ : Set where
  suc : ℕ → ℕ

f : ⊤ → Set
f tt = ℕ

{- safeButBad : ∀ x → f x → ⊤
safeButBad tt (suc y) = g tt y -}


data ⊥ : Set where

data W⊤ : Set
F⊤ = ⊥ → W⊤

data W⊤ where
  w : F⊤ → W⊤

data _<->_ (X : Set) : Set -> Set₁ where
  Refl : X <-> X

postulate
  iso : W⊤ <-> F⊤

{- bad : (X : Set) → W⊤ <-> X → X → ⊥
bad .W⊤ Refl (w x) = bad F⊤ iso x -}



