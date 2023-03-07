{-# OPTIONS --cubical #-}

module WfInitIx where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Data.Unit
open import Data.Vec as V
open import Data.Vec.Relation.Unary.All
open import Cubical.Data.Sigma

--open import Agda.Builtin.Sigma
--open import Data.Product

open import Cubical.Foundations.Equiv.Base

--open import ProgOrn.Ornaments

private variable
  ℓ : Level

data Desc : Set₁  where
  ṿ   : ℕ → Desc
  σ   : (S : Set) (D : S → Desc) → Desc

syntax σ S (λ s → D) = σ[ s ∈ S ] D

-- without-K stops us from pattern matching on ⟦ D ⟧ X
⟦_⟧ : Desc → Set → Set
⟦ ṿ n   ⟧ X = Vec X n
⟦ σ S D ⟧ X = Σ[ s ∈ S ] ⟦ D s ⟧ X
-- however, we cannot resolve this by making ⟦_⟧ data, since its level is too large

Ḟ : Desc → Set → Set
Ḟ D X = ⟦ D ⟧ X

-- so instead, we take some heavy countermeasures
data isPred (n : ℕ) : ℕ → Set where
  ispred : isPred n (suc n) 

data μ (D : Desc) (n : ℕ) : Set where
  con : ∀ {m} {p : isPred m n} → Ḟ D (μ D m) → μ D n

{-
μ-rec  : ∀ {A} → (D : Desc) → (Ḟ D A → A) → μ D → A
μ-rec-ṿ : ∀ {A : Set} {n} → (f : Vec A n → A) → ∀ m → (x : Vec (μ (ṿ n)) m) → Vec A m

μ-rec (ṿ n)    f (con x) = f (μ-rec-ṿ f n x)
μ-rec (σ S D)  f (con x) = {!!}

μ-rec-ṿ f zero    []       = []
μ-rec-ṿ f (suc m) (x ∷ xs) = (μ-rec _ f x) ∷ (μ-rec-ṿ f m xs)
-}


circle : ∀ {D : Desc} → (n : ℕ) → (E : Desc) → ⟦ E ⟧ (μ D n) → ℕ
circle _ (ṿ zero) x = 0
circle (suc n) (ṿ (suc x₁)) (con {p = ispred} x ∷ x₂) = circle n _ x + circle (suc n) _ x₂
circle _ (σ S D) x = suc (circle _ (D (fst x)) (snd x))



-- mutual
--   fold : {D : Desc} {X : Set} → (Ḟ D X → X) → μ D → X
--   fold {D = D} f (con ds) = f (mapFold D f ds)

--   mapFold : {D : Desc} (D' : Desc) → {X : Set} → (Ḟ D X → X) → ⟦ D' ⟧ (μ D) → ⟦ D' ⟧ X
--   mapFold (ṿ n)    f ds         = mapFold-Ṗ f n ds
--   mapFold (σ S D') f (s , ds)   = s , mapFold (D' s) f ds

--   mapFold-Ṗ : {D : Desc} {X : Set} → (Ḟ D X → X) → ∀ n → Vec (μ D) n → Vec X n
--   mapFold-Ṗ f zero    _        = []
--   mapFold-Ṗ f (suc n) (d ∷ ds) = ({!fold f d!} ∷ mapFold-Ṗ f n ds)



-- record Alg (X : Set) (D : Desc) : Set where
--   field
--     forget : Ḟ D X → X

-- open Alg


-- data Acc {X} (D : Desc)   (A : Alg X D) (x : X)     : Set
-- Acc' : ∀ {X} (D E : Desc) (A : Alg X D) (x : Ḟ E X) → Set

-- data Acc D A x where
--   acc : (y : fiber (A .forget) x) → Acc' D D A (fst y) → Acc D A x

-- Acc' _ (ṿ n)   A x = All (Acc _ A) x
-- Acc' _ (σ S D) A x = Acc' _ (D (fst x)) A (snd x)

-- Wf : ∀ {X} (D : Desc) → Alg X D → Set
-- Wf D A = ∀ x → Acc D A x 


-- data Primitive (A : Set) : Desc → Set₁ where
--   recurse : ∀ {n}   → (Vec A n             → A) → Primitive A (ṿ n)
--   args    : ∀ {S D} → ((s : S) → ⟦ D s ⟧ A → A) → Primitive A (σ S D)


-- try : ∀ {A} → (D : Desc) → Primitive A D → Ḟ D A → A
-- try (ṿ n) (recurse f) x = f x
-- try (σ S D) (args f) x = f (fst x) (snd x)

-- prim : ∀ {A} → (D : Desc) → Primitive A D → μ D → A
-- prim D P = μ-rec D (try D P)

-- {-
-- recV : ∀ {A : Set} {n} → (Vec A n → A) → ∀ m → Vec (μ (ṿ n)) m → Vec A m
-- recV' : ∀ {A : Set} {n} → (Vec A n → A) → μ (ṿ n) → A

-- recV f zero    x        = []
-- recV f (suc m) (x ∷ xs) = (recV' f x) ∷ (recV f m xs)

-- recV' f (con x) = f (recV f _ x)

-- {- recS' : {A : Set} {D : Desc} → Primitive A D → (E : Desc) → ⟦ E ⟧ (μ D) → ⟦ E ⟧ A
-- recS' P (ṿ zero)    []       = []
-- recS' P (ṿ (suc n)) (x ∷ xs) = {!primitive' _ P x!} ∷ (recS' P _ xs)
-- recS' P (σ S D) (s , x) = s , recS' P (D s) x -}

-- recS : ∀ {A S} {D : S → Desc} (f : (s : S) → ⟦ D s ⟧ A → A) (x : μ (σ S D)) → A
-- recS' : ∀ {A S D} (E : Desc) → (f : ⟦ E ⟧ A → A) (x : ⟦ E ⟧ (μ (σ S D))) → ⟦ E ⟧ A

-- recS f (con (s , x)) = {! f s (recS' _ (f s) x) !}

-- recS' (ṿ zero) f x = []
-- recS' (ṿ (suc n)) f (x ∷ xs) = {! recS {!!} x ∷ recS' (ṿ n) {!!} xs !}
-- recS' (σ S D) f (s , x) = {! s , recS' (D s) (λ y → f (s , y)) x !}

-- primitive' : ∀ {A} (D : Desc) → Primitive A D → μ D → A
-- primitive' (ṿ n) (recurse f) x = recV' f x
-- primitive' (σ S D) (args f) x = recS f x
-- -}

-- {-
-- -- image under poly

-- -- flip accessible
-- -- "x is accessible if it is in the image of an accessible set"

-- -- conjecture: if f : F X → X is mono and X is F-accessible, then X is F-initial
-- -- 1. note that then f is also epi, hence iso
-- -- 2. X is "not too large"
-- -- Furthermore, a map to the initial F I = I exists and is forced by accessibility?
-- -}
