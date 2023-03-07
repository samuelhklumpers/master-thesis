{-# OPTIONS --cubical #-}

module WfInitLevel where

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

data Intp (X : Set₁) : Desc → Set₁ where
  in-ṿ : ∀ {n}   → Vec X n                   → Intp X (ṿ n) 
  in-σ : ∀ {S D} → Σ[ s ∈ S ] (Intp X (D s)) → Intp X (σ S D)
  -- hacking ⟦_⟧ to work --without-K

-- bumps everything to Set₁, but that's fine because Lift
 
Ḟ : Desc → Set₁ → Set₁
Ḟ D X = Intp X D

data μ (D : Desc) : Set₁ where
  con : Ḟ D (μ D) → μ D


mutual
  fold : {D : Desc} {X : Set₁} → (Ḟ D X → X) → μ D → X
  fold {D = D} f (con ds) = f (mapFold D f ds)

  mapFold : {D : Desc} (D' : Desc) → {X : Set₁} → (Ḟ D X → X) → Intp (μ D) D' → Intp X D'
  mapFold (ṿ n)    f (in-ṿ ds)         = in-ṿ (mapFold-Ṗ f n ds)
  mapFold (σ S D') f (in-σ (s , ds))   = in-σ (s , mapFold (D' s) f ds)

  mapFold-Ṗ : {D : Desc} {X : Set₁} → (Ḟ D X → X) → ∀ n → Vec (μ D) n → Vec X n
  mapFold-Ṗ f zero    _        = []
  mapFold-Ṗ f (suc n) (d ∷ ds) = (fold f d ∷ mapFold-Ṗ f n ds)


record Alg (X : Set₁) (D : Desc) : Set₁ where
  field
    forget : Ḟ D X → X

open Alg


data Acc {X} (D : Desc) (A : Alg X D) (x : X) : Set₁
data Acc' {X} (D : Desc) (A : Alg X D) : (E : Desc) → Ḟ E X → Set₁

data Acc D A x where
  acc : (y : fiber (A .forget) x) → Acc' D A D (fst y) → Acc D A x

data Acc' D A where
  acc-ṿ : ∀ {n x}             → All (Acc D A) x  → Acc' D A (ṿ n) (in-ṿ x)
  acc-σ : ∀ {S E} {s : S} {x} → Acc' D A (E s) x → Acc' D A (σ S E) (in-σ (s , x))

Wf : ∀ {X} (D : Desc) → Alg X D → Set₁
Wf D A = ∀ x → Acc D A x 


data RecFun (A : Set₁) : Desc → Set₁ where
  recurse : ∀ {n}   → (Vec A n                → A) → RecFun A (ṿ n)
  args    : ∀ {S D} → ((s : S) → Intp A (D s) → A) → RecFun A (σ S D)

funAlg : ∀ {A} → (D : Desc) → RecFun A D → Ḟ D A → A
funAlg (ṿ n) (recurse f) (in-ṿ x) = f x
funAlg (σ S D) (args f) (in-σ (s , x)) = f s x

fix : ∀ {A} → (D : Desc) → RecFun A D → μ D → A
fix D P = fold (funAlg D P)

-- conjecture: if f : F X → X is mono and X is F-accessible, then X is F-initial
-- 1. note that then f is also epi, hence iso
-- 2. X is "not too large"
-- Furthermore, a map to the initial F I = I exists and is forced by accessibility?

thm1 : ∀ {X D} {A : Alg X D} → Wf D A → X → μ D
thm1 wf x = go x (wf x)
  where
  go   : ∀ {X D}   {A : Alg X D} x → Acc D A x → μ D
  go'  : ∀ {X D} E {A : Alg X D} x → Acc' D A E x → Ḟ E (μ D) 
  go'' : ∀ {X D} n {A : Alg X D} (x : Vec X n) → All (Acc D A) x → Vec (μ D) n 

  go x (acc (x' , p) a) = con (go' _ x' a)
  
  go' (ṿ n)   (in-ṿ x)       (acc-ṿ a) = in-ṿ (go'' n x a)
  go' (σ S D) (in-σ (s , x)) (acc-σ a) = in-σ (s , go' (D s) x a)

  go'' zero    []       a        = []
  go'' (suc n) (x ∷ xs) (ax ∷ a) = (go x ax) ∷ go'' n xs a
  -- I can't believe it actually works
