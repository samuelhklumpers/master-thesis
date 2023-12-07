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
\AgdaTarget{toℕ-Bin}
\begin{code}
toℕ-Bin : Bin → ℕ
toℕ-Bin 0b      = 0
toℕ-Bin (1b n)  = 1 + 2 * toℕ-Bin n
toℕ-Bin (2b n)  = 2 + 2 * toℕ-Bin n
\end{code}
%</Bin>

%<*Phalanx>
\AgdaTarget{Phalanx, 1p, 2p, 3p, toℕ-Phalanx}
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
\AgdaTarget{Carpal, 0c, 1c, 2c, toℕ-Carpal}
\begin{code}
data Carpal : Type where
  0c : Carpal
  1c : Carpal
  2c : Phalanx → Carpal → Phalanx → Carpal

toℕ-Carpal : Carpal → ℕ
toℕ-Carpal 0c          = 0
toℕ-Carpal 1c          = 1
toℕ-Carpal (2c l m r)  = toℕ-Phalanx l + 2 * toℕ-Carpal m + toℕ-Phalanx r
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

%<*Con-num>
\begin{code}
data Con-num : Type where
  𝟙    : ℕ → Con-num
  ρ    : ℕ → Con-num → Con-num
  σ    : (S : Type) → (S → ℕ) → Con-num → Con-num
\end{code}
%</Con-num>

\begin{code}
data U-num : Type where
  []  : U-num
  _∷_ : Con-num → U-num → U-num

infixr 5 _∷_
\end{code}

%<*Nat-num>
\begin{code}
Nat-num : U-num
Nat-num  = zeroD ∷ sucD ∷ []
  where
  zeroD  = 𝟙 0
  sucD   = ρ 1
         ( 𝟙 1 )
\end{code}
%</Nat-num>

\begin{code}

\end{code}

%<*Bin-num>
\begin{code}
Bin-num  : U-num
Bin-num  = 0bD ∷ 1bD ∷ 2bD ∷ []
  where
  0bD  = 𝟙 0 
  1bD  = ρ 2
       ( 𝟙 1 )
  2bD  = ρ 2
       ( 𝟙 2 )
\end{code}
%</Bin-num>

%<*Phalanx-num>
\begin{code}
Phalanx-num : U-num
Phalanx-num  = 1pD ∷ 2pD ∷ 3pD ∷ []
  where
  1pD  = 𝟙 1
  2pD  = 𝟙 2
  3pD  = 𝟙 3
\end{code}
%</Phalanx-num>

%<*Carpal-num>
\begin{code}
Carpal-num : U-num
Carpal-num  = 0cD ∷ 1cD ∷ 2cD ∷ []
  where
  0cD  = 𝟙 0
  1cD  = 𝟙 1
  2cD  = σ Phalanx toℕ-Phalanx  -- : Phalanx
       ( ρ 2                    -- → Carpal
       ( σ Phalanx toℕ-Phalanx  -- → Phalanx
       ( 𝟙 0 )))                -- → Carpal
\end{code}
%</Carpal-num>
