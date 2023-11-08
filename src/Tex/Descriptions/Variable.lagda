\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Descriptions.Variable where

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

data Con-var (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-var (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-var Γ I
  _∷_  : Con-var Γ ∅ I → U-var Γ I → U-var Γ I

data Con-var Γ V I where
  𝟙   : V ⊢ I → Con-var Γ V I
  ρ   : V ⊢ I → Con-var Γ V I → Con-var Γ V I
\end{code}

%<*sigma-var>
\begin{code}
  σ   : (S : V ⊢ Type) → Vxf id (V ▷ S) W → Con-var Γ W I → Con-var Γ V I
\end{code}
%</sigma-var>

\begin{code}
⟦_⟧D-var : U-var Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
data μ-var (D : U-var Γ I) (p : ⟦ Γ ⟧tel tt) : I → Type where
  con : ∀ {i} → ⟦ D ⟧D-var (μ-var D) p i → μ-var D p i

⟦_⟧C-var : Con-var Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C-var X pv i = i ≡ (j pv)
⟦ ρ j C  ⟧C-var X pv@(p , v) i = X p (j pv) × ⟦ C ⟧C-var X pv i
⟦ σ S w C  ⟧C-var X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C-var X (p , w (v , s)) i

⟦ []      ⟧D-var X p i = ⊥
⟦ C ∷ Cs  ⟧D-var X p i = ⟦ C ⟧C-var X (p , tt) i  ⊎ ⟦ Cs ⟧D-var X p i
\end{code}

%<*sigma-plus>
\begin{code}
σ+ : ∀ {V} → (S : V ⊢ Type) → Con-var Γ (V ▷ S) I → Con-var Γ V I
σ+ S C = σ S id C
\end{code}
%</sigma-plus>

%<*sigma-minus>
\begin{code}
σ- : ∀ {V} → (S : V ⊢ Type) → Con-var Γ V I → Con-var Γ V I
σ- S C = σ S fst C
\end{code}
%</sigma-minus>


