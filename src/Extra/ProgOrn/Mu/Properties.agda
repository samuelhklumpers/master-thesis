{-# OPTIONS --cubical --copatterns --postfix-projections #-}

module Extra.ProgOrn.Mu.Properties where

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Data.Vec.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation as ∥∥₁


open import Prelude hiding (rec)
open import Extra.Category
open import Extra.Category.Poly hiding (All; _∷_)
open import Extra.ProgOrn.Desc hiding (All)
import Cubical.Data.Equality as Eq


mutual
  fold : {D : Desc′} {X : Set₁} → (Ḟ D X → X) → μ D → X
  fold {D = D} f (con ds) = f (mapFold D f ds)

  mapFold : {D : Desc′} (D' : Desc′) → {X : Set₁} → (Ḟ D X → X) → Base (μ D) D' → Base X D'
  mapFold (ṿ n)    f (in-ṿ ds)         = in-ṿ (mapFold-Ṗ f n ds)
  mapFold (σ S D') f (in-σ (s , ds))   = in-σ (s , mapFold (D' s) f ds)

  mapFold-Ṗ : {D : Desc′} {X : Set₁} → (Ḟ D X → X) → ∀ n → Vec (μ D) n → Vec X n
  mapFold-Ṗ f zero    _        = []
  mapFold-Ṗ f (suc n) (d ∷ ds) = fold f d ∷ mapFold-Ṗ f n ds

map-fold : ∀ {D E} (x : Ḟ E (μ D)) (f : Ḟ D A → A) → mapFold E f x ≡ Base-map (fold f) x
map-fold-Ṗ : ∀ {D} → (f : Ḟ D A → A) → {n : ℕ} → (xs : Vec (μ D) n) → mapFold-Ṗ f n xs ≡ V.map (fold f) xs

map-fold (in-ṿ xs)      f = cong in-ṿ (map-fold-Ṗ f xs)
map-fold (in-σ (s , x)) f = cong in-σ (cong (s ,_) (map-fold x f))

map-fold-Ṗ f []       = refl
map-fold-Ṗ f (x ∷ xs) = cong (fold f x ∷_) (map-fold-Ṗ f xs)

{- data RecFun (A : Set₁) : Desc′ → Set₁ where
  recurse : ∀ {n}   → (Vec A n                → A) → RecFun A (ṿ n)
  args    : ∀ {S D} → ((s : S) → Base A (D s) → A) → RecFun A (σ S D)

funAlg : ∀ {A} → (D : Desc′) → RecFun A D → Ḟ D A → A
funAlg (ṿ n) (recurse f) (in-ṿ x) = f x
funAlg (σ S D) (args f) (in-σ (s , x)) = f s x

fix : ∀ {A} → (D : Desc′) → RecFun A D → μ D → A
fix D P = fold (funAlg D P) -}

open RawFunctor
open Functor
open Algebra
open Initial

RawḞ : (D : Desc′) → RawFunctor (ℓ-suc ℓ-zero)
RawḞ D .F₀   = Ḟ D
RawḞ D .fmap = Base-map

mapV-id : ∀ {n} → (xs : Vec A n) → V.map id xs ≡ xs
mapV-id [] = refl
mapV-id (x ∷ xs) = cong (x ∷_) (mapV-id xs)

mapV-∘ : ∀ {n} → (g : B → C) (f : A → B) (xs : Vec A n)
       → V.map (g ∘ f) xs ≡ V.map g (V.map f xs)
mapV-∘ g f [] = refl
mapV-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (mapV-∘ g f xs)

Ḟ-id : ∀ {D} → (x : Ḟ D A) → Base-map id x ≡ x
Ḟ-id (in-ṿ xs)      = cong in-ṿ (mapV-id xs)
Ḟ-id (in-σ (s , x)) = cong in-σ (cong (s ,_) (Ḟ-id x))

Ḟ-comp : ∀ {D} (g : B → C) (f : A → B) (x : Ḟ D A)
       → Base-map (g ∘ f) x ≡ Base-map g (Base-map f x)
Ḟ-comp g f (in-ṿ xs)      = cong in-ṿ (mapV-∘ _ _ _)
Ḟ-comp g f (in-σ (s , x)) = cong in-σ (cong (s ,_) (Ḟ-comp g f x))

FunḞ : (D : Desc′) → Functor (ℓ-suc ℓ-zero)
FunḞ D .RawF   = RawḞ D
FunḞ D .f-id   = Ḟ-id
FunḞ D .f-comp = Ḟ-comp

μ-Alg : (D : Desc′) → Algebra (Ḟ D)
μ-Alg D .Carrier  = μ D
μ-Alg D .forget   = con

open Alg→

InitM : (D : Desc′) → InitAlg (RawḞ D) (μ-Alg D)
InitM D .initiality AlgX = p , p!
  where
  p : Alg→ (RawḞ D) (μ-Alg D) AlgX
  p .mor = fold (AlgX .forget)
  p .coh = ∣ (funExt λ x → cong (AlgX .forget) (map-fold x (AlgX .forget))) ∣₁ 

  p! : ∀ y → ∥ p ≡ y ∥₁
  p! (alg→ f sqr) = rec squash₁ (λ s → ∣ Alg→-Path _ _ (funExt (fold≡f s)) ∣₁) sqr
    where
    module _ (sqr : Alg→-Sqr (RawḞ D) (μ-Alg D) AlgX f) where
      fold≡f : ∀ x → p .mor x ≡ f x
      help : ∀ {D} x → Base-map {D = D} (fold (AlgX .forget)) x ≡ Base-map f x
      helpV : ∀ {n} → (xs : Vec (μ D) n) → V.map (fold (AlgX .forget)) xs ≡ V.map f xs

      fold≡f (con x) = sym (funExt⁻ sqr x ∙ cong (AlgX .forget) (sym (map-fold x (AlgX .forget) ∙ help x)))

      help (in-ṿ xs)      = cong in-ṿ (helpV xs)
      help (in-σ (s , x)) = cong in-σ (cong (s ,_) (help x))

      helpV []       = refl
      helpV (x ∷ xs) = cong₂ _∷_ (fold≡f x) (helpV xs)
