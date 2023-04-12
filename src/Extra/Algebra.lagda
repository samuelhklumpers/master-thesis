\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical #-}

module Extra.Algebra where

open import Prelude

open import Cubical.Foundations.SIP
import Cubical.Structures.Auto                 as Auto


-- adapting https://agda.github.io/cubical/Cubical.Algebra.Semigroup.Base.html
\end{code}

%<*BinOp>
\begin{code}
BinOp : Type → Type
BinOp A = A → A → A
\end{code}
%</BinOp>

%<*Magma'>
\begin{code}
Magma' : Type₁
Magma' = Σ[ X ∈ Type ] (X → X → X)
\end{code}
%</Magma'>
    

%<*MagmaStr>
\begin{code}
MagmaStr : Type → Type
MagmaStr = BinOp
\end{code}
%</MagmaStr>

\begin{code}
-- not having records is unfortunate
{-
record IsMagma {A : Type} (_·_ : MagmaStr A) : Type where
  no-eta-equality
  constructor ismagma

  field
    is-set : isSet A

record MagmaStr' (A : Type) : Type where
  constructor magmastr

  field
    _·_         : MagmaStr A
    isMagma     : IsMagma _·_

  infixl 7 _·_

  open IsMagma isMagma public
-}

Magma : Type₁
Magma = TypeWithStr ℓ-zero MagmaStr

-- SIP kills levels for now :(
MagmaEquivStr = Auto.AutoEquivStr MagmaStr

MagmaUnivalentStr : UnivalentStr _ MagmaEquivStr
MagmaUnivalentStr = Auto.autoUnivalentStr MagmaStr

MagmaΣPath : (M N : Magma) → (M ≃[ MagmaEquivStr ] N) ≃ (M ≡ N)
MagmaΣPath = SIP MagmaUnivalentStr
\end{code}
\end{document}
