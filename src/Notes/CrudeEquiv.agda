{-# OPTIONS --cubical --copatterns --postfix-projections #-}

module CrudeEquiv where

open import Cubical.Functions.Embedding
open import Cubical.Relation.Binary.Base
open import Cubical.Functions.Image
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open BinaryRelation

open import Prelude


module FromEmbedding {dom cod : Type} (isSetCod : isSet cod) (e : dom ↠ cod) where
  open import Cubical.HITs.SetQuotients as SQ

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

-- this kind of statement seems to need isSet cod, but why?


module FromQER {dom cod : Type} (isSetCod : isSet cod) (e : dom ↠ cod) where
  open import Cubical.HITs.SetQuotients as SQ
  
  f = fst e

  R : dom → cod → Type
  R x y = f x ≡ y

  open import Cubical.Relation.ZigZag.Base
  open QER→Equiv
  open isQuasiEquivRel

  R' : QuasiEquivRel dom cod ℓ-zero
  R' .fst .fst = R
  R' .fst .snd a b = isSetCod (f a) b
  R' .snd .zigzag ab a'b a'b' = ab ∙∙ sym a'b ∙∙ a'b'
  R' .snd .fwd a = ∣ f a , refl ∣₁
  R' .snd .bwd b = snd e b

  Rᴿ-id : ∀ x y → Rᴿ R' x y → x ≡ y
  Rᴿ-id x y = PT.elim (λ x → isSetCod _ y) λ { (_ , b , c) → sym b ∙ c }

  main : dom / (Rᴸ R') ≃ cod / (Rᴿ R')
  main = Thm R'

