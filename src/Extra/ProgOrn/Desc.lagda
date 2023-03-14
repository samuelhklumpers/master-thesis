\documentclass[../../../Main.tex]{subfiles}

\begin{document}
\begin{code}
module Extra.ProgOrn.Desc where

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Vec as V hiding (map)
open import Function.Base

open import Level


-- Plain Descriptions
\end{code}

%<*DescS>
\AgdaTarget{Desc′}
\AgdaTarget{ṿ}
\AgdaTarget{σ}
\begin{code}
data Desc′ : Set₁  where
  ṿ   : (n : ℕ)                   → Desc′
  σ   : (S : Set) (D : S → Desc′) → Desc′
\end{code}
%</DescS>

\begin{code}
syntax σ S (λ s → D) = σ[ s ∈ S ] D



private variable
    ℓ ℓ′ : Level
    A B  : Type ℓ
    D E  : Desc′


-- The Base functor of a Description as a datatype,
-- allowing structural recursion --without-K
-- (Bumps levels)
\end{code}

%<*Base>
\AgdaTarget{Base}
\AgdaTarget{in-ṿ}
\AgdaTarget{in-σ}
\begin{code}
data Base (X : Set₁) : Desc′ → Set₁ where
  in-ṿ : ∀ {n}   → Vec X n                   → Base X (ṿ n) 
  in-σ : ∀ {S D} → Σ[ s ∈ S ] (Base X (D s)) → Base X (σ S D)
\end{code}
%</Base>

\begin{code}
un-ṿ : ∀ {n} → Base A (ṿ n) → Vec A n
un-ṿ (in-ṿ xs) = xs

un-σ : ∀ {S D} → Base A (σ S D) → Σ[ s ∈ S ] (Base A (D s))
un-σ (in-σ xs) = xs


Base-map : (A → B) → Base A D → Base B D
Base-map f (in-ṿ x)       = in-ṿ (V.map f x)
Base-map f (in-σ (s , x)) = in-σ (s , Base-map f x)


-- The least fixpoint of a Base of a Description
\end{code}
%<*mu>
\AgdaTarget{μ}
\AgdaTarget{con}
\begin{code}
data μ (D : Desc′) : Set₁ where
  con : Base (μ D) D → μ D
\end{code}
%</mu>

\begin{code}
unCon : μ D → Base (μ D) D
unCon (con x) = x


-- move to Extra.Vec
All : ∀ {n} → (P : A → Type ℓ) → Vec A n → Type ℓ
All P []       = Unit*
All P (x ∷ xs) = P x × All P xs
\end{code}
\end{document}