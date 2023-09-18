\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.DescOrn where


open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Tex.Background
\end{code}

%<*random-access>
\begin{code}
data Array (A : Type) : Type where
  Nil :                           Array A
  One : A      → Array (A × A) →  Array A
  Two : A → A  → Array (A × A) →  Array A
\end{code}
%</random-access>

%<*finger-tree>
\begin{code}
data Digit (A : Type) : Type where
  One    : A → Digit A
  Two    : A → A → Digit A
  Three  : A → A → A → Digit A

data Node (A : Type) : Type where
  Node2  : A → A → Node A
  Node3  : A → A → A → Node A

data FingerTree (A : Type) : Type where
  Empty   : FingerTree A
  Single  : A → FingerTree A

  Deep    : Digit A → FingerTree (Node A) → Digit A
          → FingerTree A
\end{code}
%</finger-tree>
\end{document}
