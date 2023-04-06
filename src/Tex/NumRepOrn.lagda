\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns #-}
module Tex.NumRepOrn where

open import Prelude hiding (⌊_⌋)
open import Data.Nat hiding (_!)
open import Data.Vec using (Vec)
open import Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Data.List hiding (fromMaybe)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Prelude.UseAs
open import Extra.TypeIsos

open import Ext.ProgOrn.Ornaments
\end{code}

%<*NatD>
\AgdaTarget{NatD}
\begin{code}
NatD : Desc ⊤ ℓ-zero
NatD _ = σ Bool λ
  { false → ṿ []
  ; true  → ṿ [ tt ] }
\end{code}
%</NatD>

%<*ListO>
\AgdaTarget{NatD-ListO}
\begin{code}
NatD-ListO : Type → OrnDesc ⊤ ! NatD
NatD-ListO A (ok _) = σ Bool λ
  { false → ṿ _
  ; true  → Δ A (λ _ → ṿ (ok _ , _)) }
\end{code}
%</ListO>

\begin{code}
NatD-VecO : Type → OrnDesc ℕ ! NatD
NatD-VecO A (ok zero)    = ∇ false (ṿ _)
NatD-VecO A (ok (suc n)) = ∇ true (Δ A (λ _ → ṿ (ok n , _)))
\end{code}

%<*LeibnizD>
\AgdaTarget{LeibnizD}
\begin{code}
LeibnizD : Desc ⊤ ℓ-zero
LeibnizD _ = σ (Fin 3) λ
  { zero             → ṿ []
  ; (suc zero)       → ṿ [ tt ]
  ; (suc (suc zero)) → ṿ [ tt ] }
\end{code}
%</LeibnizD>

Vec' : ℕ → Type → Type
Vec' n A = Vec A n

%<*TreeO>
\AgdaTarget{power}
\AgdaTarget{Two}
\AgdaTarget{LeibnizD-TreeO}
\begin{code}
power : ℕ → (A → A) → A → A
power ℕ.zero    f = λ x → x
power (ℕ.suc n) f = f ∘ power n f

Two : Type → Type
Two X = X × X

LeibnizD-TreeO : Type → OrnDesc ℕ ! LeibnizD
LeibnizD-TreeO A (ok n) = σ (Fin 3) λ
  { zero             → ṿ _
  ; (suc zero)       → Δ (power n Two A)       λ _ → ṿ (ok (suc n) , _)
  ; (suc (suc zero)) → Δ (power (suc n) Two A) λ _ → ṿ (ok (suc n) , _) }
\end{code}
%</TreeO>
\end{document}
