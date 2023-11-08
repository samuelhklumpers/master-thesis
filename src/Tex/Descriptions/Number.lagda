\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Descriptions.Number where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Data.Unit
open import Data.Nat

open import Tex.Introduction
\end{code}

data Bin : Type where
  0b       : Bin
  _1b _2b  : Bin → Bin

%<*Bin>
\begin{code}
toℕ-Bin : Bin → ℕ
toℕ-Bin 0b     = 0
toℕ-Bin (1b n) = 1 + 2 * toℕ-Bin n
toℕ-Bin (2b n) = 2 + 2 * toℕ-Bin n
\end{code}
%</Bin>

%<*Phalanx>
\begin{code}
data Phalanx : Type where
  1p 2p 3p : Phalanx

toℕ-Phalanx : Phalanx → ℕ
toℕ-Phalanx 1p = 1
toℕ-Phalanx 2p = 2
toℕ-Phalanx 3p = 3
\end{code}
%</Phalanx>

%<*Carpal>
\begin{code}
data Carpal : Type where
  0c : Carpal
  1c : Carpal
  2c : Phalanx → Carpal → Phalanx → Carpal

toℕ-Carpal : Carpal → ℕ
toℕ-Carpal 0c = 0
toℕ-Carpal 1c = 1
toℕ-Carpal (2c l m r) = toℕ-Phalanx l + 2 * toℕ-Carpal m + toℕ-Phalanx r
\end{code}
%</Carpal>

\begin{code}
data Skew′ : Type where
  start : Skew′ 
  gap   : ℕ → Skew′ → Skew′

toℕ-Skew′ : Skew′ → ℕ
toℕ-Skew′ start     = 1
toℕ-Skew′ (gap w n) = 1 + 2 ^ (suc w) * toℕ-Skew′ n 

data Skew : Type where
  zero : Skew
  bin  : Skew′ → Skew
  two  : Skew′ → ℕ → Skew

toℕ-Skew : Skew → ℕ
toℕ-Skew zero       = 0
toℕ-Skew (bin n)    = toℕ-Skew′ n
toℕ-Skew (two n w)  = 2 ^ (suc w) * (1 + toℕ-Skew′ n)
\end{code}


\begin{code}
data Con-num : Type
data U-num : Type where
  []  : U-num
  _∷_ : Con-num → U-num → U-num
  
data Con-num where
  𝟙    : ℕ → Con-num
  ρ    : ℕ → Con-num → Con-num
  σ    : (S : Type) → (S → ℕ) → Con-num → Con-num

infixr 5 _∷_
\end{code}

%<*Nat-num>
\begin{code}
Nat-num : U-num
Nat-num  = 𝟙 0
         ∷ σ ⊤ (λ _ → 1)
         ( ρ 1
         ( 𝟙 0 ))
         ∷ []
\end{code}
%</Nat-num>

\begin{code}

\end{code}

%<*Bin-num>
\begin{code}
Bin-num  : U-num
Bin-num  = 𝟙 0 
         ∷ σ ⊤ (λ _ → 1)
         ( ρ 2
         ( 𝟙 0 ))
         ∷ σ ⊤ (λ _ → 2)
         ( ρ 2
         ( 𝟙 0 ))
         ∷ []
\end{code}
%</Bin-num>

%<*Phalanx-num>
\begin{code}
Phalanx-num : U-num
Phalanx-num  = 𝟙 1
             ∷ 𝟙 2
             ∷ 𝟙 3
             ∷ []
\end{code}
%</Phalanx-num>

%<*Carpal-num>
\begin{code}
Carpal-num : U-num
Carpal-num  = 𝟙 0
            ∷ 𝟙 1
            ∷ σ Phalanx toℕ-Phalanx
            ( ρ 2
            ( σ Phalanx toℕ-Phalanx
            ( 𝟙 0 )))
            ∷ []
\end{code}
%</Carpal-num>
