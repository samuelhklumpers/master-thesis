\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Introduction where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Data.Product

private variable
  A : Type
\end{code}

%<*Bin>
\AgdaTarget{Bin, 0b, 1b, 2b, 1b\_, 2b\_}
\begin{code}
data Bin : Type where
  0b       : Bin
  1b_ 2b_  : Bin → Bin 
\end{code}
%</Bin>
%<*Random>
\AgdaTarget{Random, Zero, One, Two}
\begin{code}
data Random (A : Type) : Type where
  Zero  :                            Random A
  One   : A      → Random (A × A) →  Random A
  Two   : A → A  → Random (A × A) →  Random A
\end{code}
%</Random>

%<*size>
\begin{code}
size : Random A → Bin
size Zero           = 0b
size (One _    xs)  = 1b size xs
size (Two x y  xs)  = 2b size xs
\end{code}
%</size>
