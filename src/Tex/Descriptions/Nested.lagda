\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Descriptions.Nested where

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

%<*HMu>
\begin{code}
Fun   = Type → Type
HFun  = Fun → Fun

{-# NO_POSITIVITY_CHECK #-}
data HMu (H : HFun) (A : Type) : Type where
  con : H (HMu H) A → HMu H A 
\end{code}
%</HMu>

%<*HRandom>
\begin{code}
data HRandom (F : Fun) (A : Type) : Type where
  Zero :                       HRandom F A
  One  : A      → F (A × A) →  HRandom F A
  Two  : A → A  → F (A × A) →  HRandom F A
\end{code}
%</HRandom>

\begin{code}
try : HMu HRandom ⊤
try = con (One tt (con (One (tt , tt) (con Zero))))


data HTree (F : Fun) (A : Type) : Type where
  Zero :                         HTree F A
  One  : A      → (F A × F A) →  HTree F A
  Two  : A → A  → (F A × F A) →  HTree F A

try2 : HMu HTree ⊤
try2 = con (One tt (con (One tt (con Zero , con Zero)) , con Zero))


data HBad (F : Fun) (A : Type) : Type where
  bad : (F A → ⊥) → HBad F A

bad-is-not-ok : HMu HBad ⊤ → ⊥
bad-is-not-ok (con (bad x)) = x (con (bad x))

bad-is-ok : HMu HBad ⊤
bad-is-ok = con (bad bad-is-not-ok)

boom : ⊥
boom = bad-is-not-ok bad-is-ok

data Con-nest (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-nest (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-nest Γ I
  _∷_  : Con-nest Γ ∅ I → U-nest Γ I → U-nest Γ I

data Con-nest Γ V I where
  𝟙   : V ⊢ I → Con-nest Γ V I
\end{code}

%<*rho-nest>
\begin{code}
  ρ   : V ⊢ I → Cxf Γ Γ → Con-nest Γ V I → Con-nest Γ V I
\end{code}
%</rho-nest>

\begin{code}
  σ   : (S : V ⊢ Type) → Con-nest Γ (V ▷ S) I → Con-nest Γ V I

private variable
  Γ : Tel ⊤
  V : ExTel Γ
  I : Type

⟦_⟧C-nest : Con-nest Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C-nest X pv i = i ≡ (j pv)
\end{code}

%<*rho-nest-int>
\begin{code}
⟦ ρ j g C  ⟧C-nest X pv@(p , v) i = X (g p) (j pv) × ⟦ C ⟧C-nest X pv i
\end{code}
%</rho-nest-int>

\begin{code}
⟦ σ S C  ⟧C-nest X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C-nest X (p , v , s) i

⟦_⟧D-nest : U-nest Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
⟦ []      ⟧D-nest X p i = ⊥
⟦ C ∷ Cs  ⟧D-nest X p i = ⟦ C ⟧C-nest X (p , tt) i  ⊎ ⟦ Cs ⟧D-nest X p i
\end{code}

%<*Random>
\begin{code}
RandomD : U-nest (∅ ▷ λ _ → Type) ⊤
RandomD  = 𝟙 _
         ∷ σ (λ { ((_ , A) , _) → A })
         ( ρ _ (λ { (_ , A) → (_ , A × A) })
         ( 𝟙 _ ))
         ∷ σ (λ { ((_ , A) , _) → A })
         ( σ (λ { ((_ , A) , _) → A })
         ( ρ _ (λ { (_ , A) → (_ , A × A) })
         ( 𝟙 _ )))
         ∷ []
\end{code}
%</Random>

%<*rho0>
\begin{code}
ρ0 : ∀ {V} → V ⊢ I → Con-nest Γ V I → Con-nest Γ V I
ρ0 v C = ρ v id C
\end{code}
%</rho0>
