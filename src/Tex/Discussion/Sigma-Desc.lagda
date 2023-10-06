\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}
module Tex.Discussion.Sigma-Desc where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Function.Base
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Maybe


\end{code}

%<*Leibniz>
\begin{code}
data Leibniz : Type where
  0b       : Leibniz
  1b_ 2b_  : Leibniz → Leibniz
\end{code}
%</Leibniz>

\begin{code}

private variable
  n m : Leibniz

\end{code}

%<*FinB>
\begin{code}
data FinB : Leibniz → Type where
  0/1      : FinB (1b n)
  0/2 1/2  : FinB (2b n)

  0-1b_ 1-1b_ : FinB n → FinB (1b n)
  0-2b_ 1-2b_ : FinB n → FinB (2b n)
\end{code}
%</FinB>



%<*Sigma-Desc>
\begin{code}
data Σ-Desc (I : Type) : Type where
  𝟙 : I → Σ-Desc I
  ρ : I → Σ-Desc I → Σ-Desc I 
  σ : (S : Type) → (S → Σ-Desc I) → Σ-Desc I
\end{code}
%</Sigma-Desc>



%<*LeibnizD>
\begin{code}
LeibnizΣD : Σ-Desc ⊤
LeibnizΣD = σ (Fin 3) λ
  { zero              → 𝟙 _
  ; (suc zero)        → ρ _ (𝟙 _)
  ; (suc (suc zero))  → ρ _ (𝟙 _) }
\end{code}
%</LeibnizD>



%<*FinBD>
\begin{code}
FinBΣD : Σ-Desc Leibniz
FinBΣD = σ (Fin 3) λ
  { zero              → σ (Fin 0) λ _ → 𝟙 0b
  ; (suc zero)        → σ Leibniz λ n → σ (Fin 2) λ
    { zero        → σ (Fin 1) λ _ →        𝟙 (1b n) 
    ; (suc zero)  → σ (Fin 2) λ _ → ρ n (  𝟙 (1b n)) }
  ; (suc (suc zero))  → σ Leibniz λ n → σ (Fin 2) λ
    { zero        → σ (Fin 2) λ _ →        𝟙 (2b n) 
    ; (suc zero)  → σ (Fin 2) λ _ → ρ n (  𝟙 (2b n)) } }
\end{code}
%</FinBD>
\end{document}
