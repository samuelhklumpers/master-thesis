\documentclass[../../../Main.tex]{subfiles}

\begin{document}
\begin{code}
-- Algebras over Base functors of Descriptions and their notion of Accessibility
module Extra.Category.Poly where

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
open import Extra.Category


private variable
  ℓ ℓ′ : Level
  A B S : Type ℓ
  n : ℕ
  s : S
  x : A
  D : Desc′
  E : S → Desc′


Ḟ : Desc′ → Type₁ → Type₁
Ḟ D X = Base X D

Alg : Type₁ → Desc′ → Type₁
Alg X D = Ḟ D X → X


data All {A : Type ℓ} (P : A → Type ℓ′) : ∀ {n} → Vec A n → Set (ℓ-max ℓ ℓ′) where
  []  : All P []
  _∷_ : ∀ {x n} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Acc  (D : Desc′) (f : Alg A D) (x : A) : Set₁
data Acc' (D : Desc′) (f : Alg A D) : (E : Desc′) → Base A E → Set₁

\end{code}

%<*Acc>
\AgdaTarget{Acc}
\begin{code}
data Acc D f x where
  acc : (y : fiber f x) → Acc' D f D (fst y) → Acc D f x
\end{code}
%</Acc>

%<*Acc'>
\AgdaTarget{Acc'}
\begin{code}
data Acc' D f where
  acc-ṿ : All (Acc D f) x  → Acc' D f (ṿ n) (in-ṿ x)
  acc-σ : Acc' D f (E s) x → Acc' D f (σ S E) (in-σ (s , x))
\end{code}
%</Acc'>

\begin{code}
pre-acc : {D : Desc′} {f : Alg A D} → ∀ {x} → Acc D f x → Base A D
pre-acc (acc y _) = y .fst

Wf : ∀ {X} (D : Desc′) → Alg X D → Set₁
\end{code}
%<*Wf>
\AgdaTarget{Wf}
\begin{code}
Wf D f = ∀ x → Acc D f x
\end{code}
%</Wf>

\begin{code}
open Algebra

-- lem1 : ∀ {X D} {A : Alg X D} → AllD (λ S _ → Discrete S) D → (wf : Wf D A) → isEmbedding (thm1 wf)
-- lem1 {X = X} {D = D} {A = A} d wf = injEmbedding (isSetμ d) λ {x} {y} → {!go x y!}
--   where
--   go : ∀ x y → (a : Acc D A x) (b : Acc D A y) → thm1.go wf x x a ≡ thm1.go wf y y b → x ≡ y
--   go x y (acc (x' , px) a) (acc (y' , py) b) tp = {!!}

--   -- seems good

-- cor1 : ∀ {X D} {A : Alg X D} → AllD (λ S _ → Discrete S) D → (wf : Wf D A) → isSet X
-- cor1 d wf = Embedding-into-isSet→isSet (thm1 wf , lem1 d wf) (isSetμ d)
\end{code}
\end{document}
