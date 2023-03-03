\documentclass[Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical #-}

module Leibniz.Base where

open import Prelude
open import Extra.Algebra

import Cubical.Data.Nat.Base as N


infix 20 _1b _2b
\end{code}

The type of the 1-2 binary numbers
%<*Leibniz>
\AgdaTarget{Leibniz}
\AgdaTarget{0b}
\AgdaTarget{1b, \_1b}
\AgdaTarget{2b, \_2b}
\begin{code}
data Leibniz : Set where
    0b : Leibniz
    _1b : Leibniz → Leibniz
    _2b : Leibniz → Leibniz
\end{code}
\newcommand{\bL}{\AgdaDatatype{Leibniz}}
%</Leibniz>

The successor operation on binary numbers
%<*bsuc>
\AgdaTarget{bsuc}
\begin{code}
bsuc : Leibniz → Leibniz
bsuc 0b     = 0b 1b
bsuc (n 1b) = n 2b
bsuc (n 2b) = (bsuc n) 1b
\end{code}
%</bsuc>

Addition on binary numbers
%<*plus>
\AgdaTarget{_+_}
\begin{code}
_+_ : Leibniz → Leibniz → Leibniz
0b     + y  = y
x      + 0b = x
(x 1b) + (y 1b) = (x + y) 2b
(x 1b) + (y 2b) = bsuc (x + y) 1b
(x 2b) + (y 1b) = bsuc (x + y) 1b
(x 2b) + (y 2b) = bsuc (x + y) 2b
\end{code}
%</plus>

Right shift the binary number by a peano number of steps
%<*shiftr>
\begin{code}
_>>_ : N.ℕ → Leibniz → Leibniz
ℕ.zero  >> y      = y
ℕ.suc x >> 0b     = 0b
ℕ.suc x >> (y 1b) = x >> y
ℕ.suc x >> (y 2b) = x >> y
\end{code}
%</shiftr>

\begin{code}
infix 6 _<_ _≤_
\end{code}

Inequality on binary numbers
\begin{code}
data _<_ : Leibniz → Leibniz → Type
_≤_ : Leibniz → Leibniz → Type

data _<_ where
  0b<1b :         0b   < y 1b
  0b<2b :         0b   < y 2b
  1b<1b : x < y → x 1b < y 1b
  1b<2b : x ≤ y → x 1b < y 2b
  2b<1b : x < y → x 2b < y 1b
  2b<2b : x < y → x 2b < y 2b

x ≤ y = (x < y) ⊎ (x ≡ y)
\end{code}

From peano to leibniz
%<*fromN>
\AgdaTarget{fromℕ}
\begin{code}
fromℕ : ℕ → Leibniz
fromℕ ℕ.zero    = 0b
fromℕ (ℕ.suc n) = bsuc (fromℕ n)
\end{code}
%</fromN>

From leibniz to peano
%<*toN>
\AgdaTarget{toℕ}
\begin{code}
toℕ : Leibniz → ℕ
toℕ 0b     = 0
toℕ (n 1b) = 1 N.+ 2 N.· toℕ n 
toℕ (n 2b) = 2 N.+ 2 N.· toℕ n
\end{code}
%</toN>
\end{document}
