\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Descriptions.Composite where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Function.Base

open import Tex.Background

private variable
  A B C : Type
\end{code}


\begin{code}
private variable
  Γ Δ : Tel ⊤
  V W : ExTel Γ
  I J : Type

data Con-comp (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-comp (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-comp Γ I
  _∷_  : Con-comp Γ ∅ I → U-comp Γ I → U-comp Γ I

data Con-comp Γ V I where
  𝟙   : V ⊢ I → Con-comp Γ V I
  ρ   : V ⊢ I → Con-comp Γ V I → Con-comp Γ V I
  σ   : (S : V ⊢ Type) → Con-comp Γ (V ▷ S) I → Con-comp Γ V I
\end{code}

%<*delta>
\begin{code}
  δ   : (R : U-comp Δ J) (d : Cxf Γ Δ) (j : I → J)
      → Con-comp Γ V I → Con-comp Γ V I
\end{code}
%</delta>

\begin{code}
⟦_⟧D-comp : U-comp Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
data μ-comp (D : U-comp Γ I) (p : ⟦ Γ ⟧tel tt) : I → Type where
  con : ∀ {i} → ⟦ D ⟧D-comp (μ-comp D) p i → μ-comp D p i

⟦_⟧C-comp : Con-comp Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C-comp X pv i = i ≡ (j pv)
⟦ ρ j C  ⟧C-comp X pv@(p , v) i = X p (j pv) × ⟦ C ⟧C-comp X pv i
⟦ σ S C  ⟧C-comp X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C-comp X (p , v , s) i
\end{code}

%<*delta-int>
\begin{code}
⟦ δ R d j C  ⟧C-comp  X pv@(p , v) i
                      = μ-comp R (d p) (j i) × ⟦ C ⟧C-comp X pv i
\end{code}
%</delta-int>

\begin{code}
⟦ []      ⟧D-comp X p i = ⊥
⟦ C ∷ Cs  ⟧D-comp X p i = ⟦ C ⟧C-comp X (p , tt) i  ⊎ ⟦ Cs ⟧D-comp X p i
\end{code}


