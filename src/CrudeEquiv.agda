{-# OPTIONS --cubical #-}

module CrudeEquiv where

open import Cubical.Functions.Embedding
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Relation.Binary.Base
open import Cubical.Functions.Image
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open BinaryRelation

open import Prelude


module _ {dom cod : Type} (isSetCod : isSet cod) (e : dom ↠ cod) where
  f = fst e
 
  ∼f : dom → dom → Type
  ∼f x y = f x ≡ f y

  dom' : Type
  dom' = dom / ∼f

  f' : dom' → cod
  f' = SQ.rec isSetCod f (λ a b r → r)

  f-inj : ∀ x y → f' x ≡ f' y → x ≡ y
  f-inj = elimProp2 (λ x y → isPropΠ (λ _ → squash/ x y)) λ a b → eq/ a b
  
  isEmbedding-f' : isEmbedding f'
  isEmbedding-f' = injEmbedding isSetCod (f-inj _ _)

  isSurjection-f' : isSurjection f'
  isSurjection-f' x = PT.rec squash₁ (λ { (y , p) → ∣ [ y ] , p ∣₁ }) (snd e x)

  crude : dom' ≃ cod
  crude = f' , isEmbedding×isSurjection→isEquiv (isEmbedding-f' , isSurjection-f')



{- -- puzzle for another time, can we get away with less? 
module _ {dom cod : Type} (e : dom ↠ cod) where
  f = fst e
 
  ∼f : dom → dom → Type
  ∼f x y = f x ≡ f y

  dom' : Type
  dom' = dom /ₜ ∼f

  f' : dom' → cod
  f' = SQ.rec f (λ a b r → r)

  f'-inj : ∀ x y → f' x ≡ f' y → x ≡ y
  f'-inj [ a ] [ b ] p = eq/ a b p
  f'-inj [ a ] (eq/ x y r i) p j = {!eq/ a (eq/ x y r i) p j!}
  f'-inj (eq/ a b r i) [ a₁ ] p = {!!}
  f'-inj (eq/ a b r i) (eq/ a₁ b₁ r₁ i₁) p = {!!}

  f-embed : dom' ↪ cod
  f-embed = f' , h₂
    where
    h₁ : ∀ {x y} → (p : f' x ≡ f' y) → isContr (fiber (cong {x = x} {y = y} f') p)
    h₁ p = ({!!} , {!!}) , {!!}

    h₂ : ∀ x y → isEquiv (cong {x = x} {y = y} f')
    h₂ x y = record { equiv-proof = h₁ }


  crude : dom' ≃ cod
  crude = f' , {!isEquivEmbeddingOntoImage (!}
-}
