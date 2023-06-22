\begin{document}
\begin{code}
module Tex.Background where

--open import Agda.Builtin.Cubical.Path
--open import Data.Bool
--open import Function.Base
open import Data.Nat hiding (_+_)

private variable
  A B C : Set
\end{code}

\begin{code}
Type = Set
\end{code}

%<*bool>
\begin{code}
data Bool : Type where
    false  : Bool
    true   : Bool 
\end{code}
%</bool>


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
data ⊥ : Type where
\end{code}
%</false>

\begin{code}
¬_ : Type → Type
¬ A = A → ⊥
\end{code}


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

%<*distr>
\begin{code}
→-×-undistr : ((A → C) × (B → C)) → (A + B) → C
→-×-undistr (a→c , b→c) (inl a) = a→c a
→-×-undistr (a→c , b→c) (inr b) = b→c b
\end{code}
%</distr>

%<*fin>
\begin{code}
data Fin : ℕ → Type where
  zero  : ∀ {n}          → Fin (suc n)
  suc   : ∀ {n} → Fin n  → Fin (suc n)
\end{code}
%</fin>

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
