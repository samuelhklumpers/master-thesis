-- https://github.com/agda/agda/issues/5910#issuecomment-1601301237

{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

data Zero : Set where

data Id (X : Set) : Set where
  i : X → Id X

mutual
  data WOne : Set where wrap : Id FOne -> WOne
  FOne = Zero -> WOne

data _<->_ (X : Set) : Set -> Set₁ where
  Refl : X <-> X

isom : Iso WOne FOne
isom =
  iso
    (λ _ ())
    (λ f → wrap (i f))
    (λ _ → funExt λ ())
    (λ { (wrap (i _)) → cong (λ f → wrap (i f)) (funExt λ ()) })

eq : WOne <-> FOne
eq = subst (λ X → WOne <-> X) (isoToPath isom) Refl

noo : (X : Set) -> (WOne <-> X) -> Id X -> Zero
noo .WOne Refl (i (wrap f)) = noo FOne eq f

absurd : Zero
absurd = noo FOne eq (i \ ())
