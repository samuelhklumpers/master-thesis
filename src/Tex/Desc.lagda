\begin{code}[hide] 
module Tex.Desc where

open import Agda.Primitive renaming (Set to Type)
open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Relation.Binary.PropositionalEquality
open import Function.Base
\end{code}

\begin{code}[hide]
module Finite where
\end{code}

%<*blab>
\begin{code}
  data Desc : Type where
    𝟘 𝟙      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
%</blab>

%<*blab>
\begin{code}
  μ : Desc → Type
  μ 𝟘        = ⊥
  μ 𝟙        = ⊤
  μ (D ⊕ E)  = μ D ⊎ μ E
  μ (D ⊗ E)  = μ D × μ E
\end{code}
%</blab>

%<*blab>
\begin{code}
  BoolD : Desc
  BoolD = 𝟙 ⊕ 𝟙
\end{code}
%</blab>

%<*blab>
\begin{code}
data ℕ : Type where
  zero  : ℕ
  suc   : ℕ → ℕ 
\end{code}
%</blab>

\begin{code}[hide]
module Recursive where
  data Desc : Type
\end{code}

%<*blab>
\begin{code}
  ⟦_⟧ : Desc → Type → Type
\end{code}
%</blab>

%<*blab>
\begin{code}
  data μ (D : Desc) : Type where
    con : ⟦ D ⟧ (μ D) → μ D
\end{code}
%</blab>

%<*blab>
\begin{code}
  data Desc where
    𝟙 ρ      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
%</blab>

%<*blab>
\begin{code}
  ⟦ 𝟙      ⟧ X = ⊤
  ⟦ ρ      ⟧ X = X
  ⟦ D ⊕ E  ⟧ X = (⟦ D ⟧ X) ⊎ (⟦ E ⟧ X)
  ⟦ D ⊗ E  ⟧ X = (⟦ D ⟧ X) × (⟦ E ⟧ X)
\end{code}
%</blab>

%<*blab>
\begin{code}
  ℕD  : Desc
  ℕD  = 𝟙 ⊕ ρ
\end{code}
%</blab>

\begin{code}[hide]
module NearSOP where
\end{code}

%<*blab>
\begin{code}
  data Desc : Type₁ where
    𝟙    : Desc
    ρ    : Desc → Desc
    σ    : (S : Type) → (S → Desc) → Desc
    _⊕_  : Desc → Desc → Desc
\end{code}
%</blab>

%<*blab>
\begin{code}
  ListD : Type → Desc
  ListD A = 𝟙 ⊕ (σ A λ _ → ρ 𝟙) 
\end{code}
%</blab>

\begin{code}[hide]
module Indexed where
  private variable
    I : Type
\end{code}

%<*blab>
\begin{code}
  data Desc (I : Type) : Type₁ where
    𝟙    : I → Desc I
    ρ    : I → Desc I → Desc I
    σ    : (S : Type) → (S → Desc I) → Desc I
    _⊕_  : Desc I → Desc I → Desc I
\end{code}
%</blab>

%<*blab>
\begin{code}
  ⟦_⟧ : Desc I → (I → Type) → (I → Type)
  ⟦ 𝟙 j    ⟧ X i = i ≡ j
  ⟦ ρ j D  ⟧ X i = X j × ⟦ D ⟧ X i
  ⟦ σ S D  ⟧ X i = Σ[ s ∈ S ] ⟦ D s ⟧ X i
  ⟦ D ⊕ E  ⟧ X i = ⟦ D ⟧ X i ⊎ ⟦ E ⟧ X i
\end{code}
%</blab>

%<*blab>
\begin{code}
  VecD : Type → Desc ℕ
  VecD A = (𝟙 zero) ⊕ (σ ℕ λ n → σ A λ _ → ρ n (𝟙 (suc n)))
\end{code}
%</blab>

\begin{code}[hide]
module Tele where
\end{code}

%<*blab>
\begin{code}
  data Tel : Type₁
  ⟦_⟧tel : Tel → Type
  
  data Tel where
    ∅    : Tel
    _▷_  : (Γ : Tel) (S : ⟦ Γ ⟧tel → Type) → Tel
\end{code}
%</blab>

\begin{code}[hide]
  ⟦ ∅      ⟧tel = ⊤
  ⟦ Γ ▷ S  ⟧tel = Σ ⟦ Γ ⟧tel S
\end{code}

\begin{code}[hide]
module Parameter where
  private variable
    a : Level
    P : Type
\end{code}

%<*blab>
\begin{code}
  data Tel (P : Type) : Type₁
  ⟦_⟧tel : Tel P → P → Type
  _⊢_ : Tel P → Type a → Type a
  Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A
  
  data Tel P where
    ∅    : Tel P
    _▷_  : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P
\end{code}
%</blab>

%<*blab>
\begin{code}
  ⟦ ∅      ⟧tel p = ⊤
  ⟦ Γ ▷ S  ⟧tel p = Σ[ x ∈ ⟦ Γ ⟧tel p ] S (p , x)
\end{code}
%</blab>

%<*blab>
\begin{code}
  ExTel : Tel ⊤ → Type₁
  ExTel Γ = Tel (⟦ Γ ⟧tel tt)
\end{code}
%</blab>

\begin{code}[hide]
  private variable
    Γ Δ : Tel P
    V W : ExTel Γ
    I : Type
\end{code}

%<*blab>
\begin{code}
  ⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
  ⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel
\end{code}
%</blab>

%<*blab>
\begin{code}
  data Con (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type₁
  data Desc (Γ : Tel ⊤) (I : Type) : Type₁ where
    []   : Desc Γ I
    _∷_  : Con Γ ∅ I → Desc Γ I → Desc Γ I
\end{code}
%</blab>

%<*blab>
\begin{code}
  data Con Γ V I where
    𝟙   : V ⊢ I → Con Γ V I
    ρ   : V ⊢ I → Con Γ V I → Con Γ V I
    σ   : (S : V ⊢ Type) → Con Γ (V ▷ S) I → Con Γ V I
\end{code}
%</blab>

%<*blab>
\begin{code}
  ⟦_⟧C : Con Γ V I → (⟦ Γ & V ⟧tel → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
  ⟦ 𝟙 j    ⟧C X pv i = i ≡ (j pv)
  ⟦ ρ j C  ⟧C X pv i = X pv (j pv) × ⟦ C ⟧C X pv i
  ⟦ σ S C  ⟧C X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C (X ∘ map₂ proj₁) (p , v , s) i

  ⟦_⟧D : Desc Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
  ⟦ []      ⟧D X p i = ⊥
  ⟦ C ∷ Cs  ⟧D X p i = ⟦ C ⟧C (X ∘ proj₁) (p , tt) i  ⊎ ⟦ Cs ⟧D X p i
\end{code}
%</blab>

%<*blab>
\begin{code}
  data μ (D : Desc Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
    con : ⟦ D ⟧D (μ D) p i → μ D p i
\end{code}
%</blab>
