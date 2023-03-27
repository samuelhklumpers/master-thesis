module Flex-2Sided where


open import Function.Base using (_$_)

open import Cubical.Data.Maybe
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Prelude hiding (⌊_⌋; _◁_; _▷_)
open import Twosided-Triefy

open import ProgOrn.Ornaments hiding (_⋈_)



record Flex-2Sided (Arr : Type → Type) : Type₁ where
  field
    head : Arr A → Maybe A
    last : Arr A → Maybe A
    cons : A → Arr A → Arr A
    snoc : Arr A → A → Arr A

  field
    sccs : ∀ (x : A) y xs → snoc (cons x xs) y ≡ cons x (snoc xs y)
    hc   : ∀ (x : A) xs   → head (cons x xs)   ≡ just x
    ls   : ∀ xs (x : A)   → last (snoc xs x)   ≡ just x
    --       ^ I didn't know Agda would be ok with solving this to A
