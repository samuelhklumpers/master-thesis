-- Algebras over Base functors of Descriptions and their notion of Accessibility
module PolyAlgebras where

open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Data.Vec.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Properties
open import Data.Nat
open import Data.Unit

import Cubical.Data.Equality as Eq

open import Extra.ProgOrn.Desc hiding (All)
open import Extra.ProgOrn.Desc.Properties
open import Category


private variable
  ℓ ℓ′ : Level
  A B  : Type ℓ
  D : Desc


Ḟ : Desc → Type₁ → Type₁
Ḟ D X = Base X D

Alg : Type₁ → Desc → Type₁
Alg X D = Ḟ D X → X


data All {A : Type ℓ} (P : A → Type ℓ′) : ∀ {n} → Vec A n → Set (ℓ-max ℓ ℓ′) where
  []  : All P []
  _∷_ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Acc  (D : Desc) (f : Alg A D) (x : A) : Set₁
data Acc' (D : Desc) (f : Alg A D) : (E : Desc) → Base A E → Set₁

data Acc D f x where
  acc : (y : fiber f x) → Acc' D f D (fst y) → Acc D f x
data Acc' D f where
  acc-ṿ : ∀ {n x}             → All (Acc D f) x  → Acc' D f (ṿ n) (in-ṿ x)
  acc-σ : ∀ {S E} {s : S} {x} → Acc' D f (E s) x → Acc' D f (σ S E) (in-σ (s , x))

Wf : ∀ {X} (D : Desc) → Alg X D → Set₁
Wf D A = ∀ x → Acc D A x


-- conjecture: if f : F X → X is mono and X is F-accessible, then X is F-initial
-- 1. note that then f is also epi, hence iso
-- 2. X is "not too large"
-- Furthermore, a map to the initial F I = I exists and is forced by accessibility?

thm1 : ∀ {X D} {A : Alg X D} → Wf D A → X → μ D
thm1 {X = X} {D = D} {A = A} wf x = go x (wf x)
  module thm1 where
  go   : ∀ x → Acc D A x → μ D
  go'  : ∀ E x → Acc' D A E x → Base (μ D) E 
  go'' : ∀ n (x : Vec X n) → All (Acc D A) x → Vec (μ D) n 

  go x (acc (x' , p) a) = con (go' _ x' a)
  
  go' (ṿ n)   (in-ṿ x)       (acc-ṿ a) = in-ṿ (go'' n x a)
  go' (σ S D) (in-σ (s , x)) (acc-σ a) = in-σ (s , go' (D s) x a)

  go'' zero    []       a        = []
  go'' (suc n) (x ∷ xs) (ax ∷ a) = (go x ax) ∷ go'' n xs a
  -- I can't believe it actually works


-- lem1 : ∀ {X D} {A : Alg X D} → AllD (λ S _ → Discrete S) D → (wf : Wf D A) → isEmbedding (thm1 wf)
-- lem1 {X = X} {D = D} {A = A} d wf = injEmbedding (isSetμ d) λ {x} {y} → {!go x y!}
--   where
--   go : ∀ x y → (a : Acc D A x) (b : Acc D A y) → thm1.go wf x x a ≡ thm1.go wf y y b → x ≡ y
--   go x y (acc (x' , px) a) (acc (y' , py) b) tp = {!!}

--   -- seems good

-- cor1 : ∀ {X D} {A : Alg X D} → AllD (λ S _ → Discrete S) D → (wf : Wf D A) → isSet X
-- cor1 d wf = Embedding-into-isSet→isSet (thm1 wf , lem1 d wf) (isSetμ d)

-- Alg→Algebra : (f : Alg A D) → Wf D f → Algebra (Ḟ D)
-- Alg→Algebra f wf = {!!}
