\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical #-}

module Tex.Flatten where

open import Prelude hiding (⌊_⌋)
open import ProgOrn.Ornaments

open import Data.List
open import Data.Vec using (Vec)

import Cubical.Data.Nat as N
import Data.Fin as Fin
open import Data.Bool
open import Data.Fin hiding (toℕ)
\end{code}

%<*RField>
\AgdaTarget{RField}
\begin{code}
RField : RDesc ⊤ → Type
RField (ṿ is)  = ⊤
RField (σ S D) = Σ S λ s → RField (D s)
\end{code}
%</RField>

%<*Number>
\AgdaTarget{Number}
\AgdaTarget{𝟙}
\AgdaTarget{ṿ}
\begin{code}
-- note to self, I should probably make ṿ _not_ overlap
-- so not everything links here
data Number : Type where
  𝟙 : Number
  ṿ : ∀ n → (Fin n → Number) → Number
\end{code}
%</Number>

%<*RSize>
\AgdaTarget{RSize}
\begin{code}
RSize : (d : RDesc ⊤) → (a : RField d) → ℕ
RSize (ṿ is)  a = length is
RSize (σ S D) a = RSize (D (fst a)) (snd a)
\end{code}
%</RSize>

%<*Fields>
\AgdaTarget{Fields}
\AgdaTarget{leaf}
\AgdaTarget{node}
\begin{code}
data Fields (d : RDesc ⊤) : Number → Type where
  leaf : RField d → Fields d 𝟙
  node : ∀ n {f : Fin n → Number}
       → ((i : Fin n) → Fields d (f i)) → Fields d (ṿ n f)   
\end{code}
%</Fields>

%<*subnodes>
\AgdaTarget{subnodes}
\begin{code}
subnodes : ∀ {n} {d : RDesc ⊤} → Fields d n → Number
subnodes (leaf x)   = ṿ (RSize _ x) λ _ → 𝟙
subnodes (node n f) = ṿ n (subnodes ∘ f)
\end{code}
%</subnodes>

%<*nested>
\AgdaTarget{nested}
\begin{code}
nested : Desc ⊤ → Desc Number
nested d n = σ (Fields (d tt) n) λ a → ṿ [ subnodes a ]
\end{code}
%</nested>


\begin{code}
record Dummy : Type₁ where
    field
\end{code}
%<*wish>
\begin{code}
        nested-eq : ∀ D → μ D tt ≃ μ (nested D) 𝟙
\end{code}
%</wish>

tmp : {E : Desc ⊤} → (d : RDesc ⊤) → ⟦ d ⟧ (μ E) → RField d
tmp (ṿ is)  x = tt
tmp (σ S D) x = fst x , tmp (D (fst x)) (snd x)

module _ (D : Desc ⊤) where
  left = μ D tt
  D' = nested D
  right = μ D'

  to : left → right 𝟙
  to (con x) = con (leaf (tmp (D tt) x) , {!!} , _)
