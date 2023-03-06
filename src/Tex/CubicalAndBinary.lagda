\documentclass[../Main.tex]{subfiles}


\begin{document}
%<*cubical>
\begin{code}
{-# OPTIONS --cubical #-} 
\end{code}
%</cubical>

\begin{code}[hide]
module Tex.CubicalAndBinary where

open import Cubical.Foundations.Prelude hiding (sym; funExt)
open import Leibniz.Base
open import Leibniz.Properties
import Cubical.Data.Nat as N

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Glue public
  using (Glue ; glue ; unglue)

open import Cubical.Reflection.StrictEquiv

private variable
    ℓ ℓ′ : Level
    A B : Type
    x y : A
    f g : A → B
\end{code}

%<*Peano>
\AgdaTarget{ℕ}
\AgdaTarget{zero}
\AgdaTarget{suc}
\begin{code}
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
\end{code}
%</Peano>

%<*sym>
\AgdaTarget{sym}
\begin{code}
sym : x ≡ y → y ≡ x
sym p i = p (~ i)
\end{code}
%</sym>

%<*funExt>
\AgdaTarget{funExt}
\begin{code}
funExt : (∀ x → f x ≡ g x) → f ≡ g 
funExt p i x = p x i
\end{code}
%</funExt>

%<*ua>
\begin{code}
ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
\end{code}
\begin{code}[hide]
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })
\end{code}
%</ua>

%<*badplus>
\begin{code}
BinOp : Type → Type
BinOp A = A → A → A

_+′_ : BinOp Leibniz
_+′_ = subst BinOp ℕ≡L N._+_
\end{code}
%</badplus>
\end{document}
