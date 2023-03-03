\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical #-}

module Prelude.UseAs where

open import Prelude

private variable
  a b : Level
\end{code}

Often we're in a situation where we have naive definition of some algorithm on one side, and an optimized definition on the other side. Then we usually proceed by proving equivalence of the definitions, so that we can show correctness of the optimized definition.

Wouldn't it be nice if we got the optimized definition and its correctness for free?
Let's try.


%<*isigma>
\AgdaTarget{Σ'}
\AgdaTarget{use-as-def, \_use-as-def}
\begin{code}
record Σ' (A : Set a) (B : A → Set b) : Set (ℓ-max a b) where
  constructor _use-as-def
  field
    {fst} : A
    snd : B fst

open Σ'

infix 1 _use-as-def
\end{code}
%</isigma>

%<*Def>
\AgdaTarget{Def}
\AgdaTarget{defined-by}
\AgdaTarget{by-definition}
\begin{code}
Def : {X : Type a} → X → Type a
Def {X = X} x = Σ' X λ y → x ≡ y

defined-by : {X : Type a} {x : X} → Def x → X
defined-by = fst

by-definition : {X : Type a} {x : X} → (d : Def x) → x ≡ defined-by d
by-definition = snd
\end{code}
%</Def>
\end{document}
