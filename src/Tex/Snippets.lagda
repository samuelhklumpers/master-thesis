\documentclass[../Main.tex]{subfiles}


\begin{document}
\begin{code}
module Tex.Snippets where

open import Agda.Builtin.Cubical.Path
open import Data.Bool
open import Level

private variable
  ℓ : Level
  A B C : Set


module Contr where
  open import Cubical.Data.Sigma.Base

  isContr : Type ℓ → Type ℓ
  \end{code}
  %<*isContr>
  \AgdaTarget{isContr}
  \begin{code}
  isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)
  \end{code}
  %</isContr>

\begin{code}
Type = Set
\end{code}

%<*ternary>
\begin{code}
_🍧_🌶_ : Bool → A → A → A
false 🍧 t 🌶 e = e
true 🍧 t 🌶 e = t
\end{code}
%</ternary>

%<*true>
\begin{code}
record ⊤ : Type where
  constructor tt
\end{code}
%</true>


%<*false>
\begin{code}
record ⊥ : Type where
\end{code}
%</false>

%<*either>
\begin{code}
data _+_ A B : Type where
  inl : A → A + B
  inr : B → A + B
\end{code}
%</either>

%<*pair>
\begin{code}
record _×_ A B : Type where
  constructor _,_
  field
    fst : A
    snd : B
\end{code}
%</pair>

\begin{code}
private variable
\end{code}
%<*predicate>
\begin{code}
  P : A → Type
\end{code}
%</predicate>


%<*exists>
\begin{code}
record ∃ A (P : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : P fst
\end{code}
%</exists>

\begin{code}
module _ (x :
\end{code}
%<*forall>
\begin{code}
  (a : A) → P a
\end{code}
%</forall>
\begin{code}
  ) where
\end{code}

%<*eq>
\begin{code}
data Eq (a : A) : A → Type where
  refl : Eq a a
\end{code}
%</eq>

\begin{code}
private variable
  a b : A
\end{code}

%<*subst>
\begin{code}
subst : Eq a b → P a → P b
subst refl x = x
\end{code}
%</subst>


\begin{code}
{-# TERMINATING #-}
\end{code}
%<*loop>
\begin{code}
undefined : ∀ {A : Type} → A
undefined = undefined
\end{code}
%</loop>

\end{document}
