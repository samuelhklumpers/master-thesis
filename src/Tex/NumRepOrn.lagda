\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns #-}
module Tex.NumRepOrn where

open import Prelude hiding (⌊_⌋)
open import Data.Nat hiding (_!)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Data.List hiding (fromMaybe)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Prelude.UseAs
open import TypeIsos

open import ProgOrn.Ornaments hiding (NatD; VecD)
\end{code}

\begin{code}
NatD : Desc ⊤
NatD _ = σ Bool λ
  { false → ṿ []
  ; true  → ṿ [ tt ] }
\end{code}

\begin{code}
NatD-VecO : Type → OrnDesc ℕ ! NatD
NatD-VecO A (ok zero)    = ∇ false (ṿ _)
NatD-VecO A (ok (suc n)) = ∇ true (Δ A (λ _ → ṿ (ok n , _)))
\end{code}

\end{document}
