{-# OPTIONS --cubical #-}

module Extra.TypeIsos where

open import Prelude


⊥-strict : (A → ⊥) → A ≡ ⊥
⊥-strict f = ua (uninhabEquiv f λ ())
