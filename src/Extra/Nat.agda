{-# OPTIONS --cubical --copatterns #-}

module Extra.Nat where

open import Prelude
open import Extra.Algebra
open import Extra.Algebra.Definitions

open import Cubical.Data.Nat


Magmaℕ : Magma
fst Magmaℕ = ℕ
snd Magmaℕ = _+_

ℕ-assoc : Associative _≡_ (snd Magmaℕ)
ℕ-assoc x y z = sym (+-assoc x y z) -- why is Cubical like this?
