\begin{code}[hide] 
{-# OPTIONS --type-in-type -W noUnreachableClauses #-}

module Tex.Desc where

open import Agda.Primitive renaming (Set to Type)
open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Relation.Binary.PropositionalEquality hiding (J)
open import Function.Base
\end{code}

\begin{code}[hide]
module Finite where
\end{code}

%<*fin-desc>
\begin{code}
  data Desc : Type where
    𝟘 𝟙      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
%</fin-desc>

%<*fin-mu>
\begin{code}
  μ : Desc → Type
  μ 𝟘        = ⊥
  μ 𝟙        = ⊤
  μ (D ⊕ E)  = μ D ⊎ μ E
  μ (D ⊗ E)  = μ D × μ E
\end{code}
%</fin-mu>

%<*BoolD>
\begin{code}
  BoolD : Desc
  BoolD = 𝟙 ⊕ 𝟙
\end{code}
%</BoolD>

%<*Nat>
\begin{code}
data ℕ : Type where
  zero  : ℕ
  suc   : ℕ → ℕ 
\end{code}
%</Nat>

\begin{code}[hide]
module Recursive where
  data Desc : Type
\end{code}

%<*rec-intp-type>
\begin{code}
  ⟦_⟧ : Desc → Type → Type
\end{code}
%</rec-intp-type>

%<*rec-mu>
\begin{code}
  data μ (D : Desc) : Type where
    con : ⟦ D ⟧ (μ D) → μ D
\end{code}
%</rec-mu>

%<*rec-desc>
\begin{code}
  data Desc where
    𝟙 ρ      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
%</rec-desc>

%<*rec-intp>
\begin{code}
  ⟦ 𝟙      ⟧ X = ⊤
  ⟦ ρ      ⟧ X = X
  ⟦ D ⊕ E  ⟧ X = (⟦ D ⟧ X) ⊎ (⟦ E ⟧ X)
  ⟦ D ⊗ E  ⟧ X = (⟦ D ⟧ X) × (⟦ E ⟧ X)
\end{code}
%</rec-intp>

%<*NatD>
\begin{code}
  ℕD  : Desc
  ℕD  = 𝟙 ⊕ ρ
\end{code}
%</NatD>

\begin{code}[hide]
module NearSOP where
\end{code}

%<*field-desc>
\begin{code}
  data Desc : Type₁ where
    𝟙    : Desc
    ρ    : Desc → Desc
    σ    : (S : Type) → (S → Desc) → Desc
    _⊕_  : Desc → Desc → Desc
\end{code}
%</field-desc>

%<*ListD>
\begin{code}
  ListD : Type → Desc
  ListD A = 𝟙 ⊕ (σ A λ _ → ρ 𝟙) 
\end{code}
%</ListD>

\begin{code}[hide]
module Indexed where
  private variable
    I : Type
\end{code}

%<*idesc>
\begin{code}
  data Desc (I : Type) : Type₁ where
    𝟙    : I → Desc I
    ρ    : I → Desc I → Desc I
    σ    : (S : Type) → (S → Desc I) → Desc I
    _⊕_  : Desc I → Desc I → Desc I
\end{code}
%</idesc>

%<*iintp>
\begin{code}
  ⟦_⟧ : Desc I → (I → Type) → (I → Type)
  ⟦ 𝟙 j    ⟧ X i = i ≡ j
  ⟦ ρ j D  ⟧ X i = X j × ⟦ D ⟧ X i
  ⟦ σ S D  ⟧ X i = Σ[ s ∈ S ] ⟦ D s ⟧ X i
  ⟦ D ⊕ E  ⟧ X i = ⟦ D ⟧ X i ⊎ ⟦ E ⟧ X i
\end{code}
%</iintp>

%<*VecD>
\begin{code}
  VecD : Type → Desc ℕ
  VecD A = (𝟙 zero) ⊕ (σ ℕ λ n → σ A λ _ → ρ n (𝟙 (suc n)))
\end{code}
%</VecD>

\begin{code}[hide]
module Tele where
\end{code}

%<*Tel-simple>
\begin{code}
  data Tel : Type₁
  ⟦_⟧tel : Tel → Type
  
  data Tel where
    ∅    : Tel
    _▷_  : (Γ : Tel) (S : ⟦ Γ ⟧tel → Type) → Tel
\end{code}
%</Tel-simple>

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

%<*Tel>
\begin{code}
  data Tel (P : Type) : Type
  ⟦_⟧tel : Tel P → P → Type
  _⊢_ : Tel P → Type → Type
  Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A
  
  data Tel P where
    ∅    : Tel P
    _▷_  : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P
\end{code}
%</Tel>

%<*Tel-intp>
\begin{code}
  ⟦ ∅      ⟧tel p = ⊤
  ⟦ Γ ▷ S  ⟧tel p = Σ[ x ∈ ⟦ Γ ⟧tel p ] S (p , x)
\end{code}
%</Tel-intp>

%<*ExTel>
\begin{code}
  ExTel : Tel ⊤ → Type₁
  ExTel Γ = Tel (⟦ Γ ⟧tel tt)
\end{code}
%</ExTel>

\begin{code}[hide]
  private variable
    Γ Δ : Tel P
    V W : ExTel Γ
    I : Type
\end{code}

%<*Extel-intp>
\begin{code}
  ⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
  ⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel
\end{code}
%</Extel-intp>

%<*sop-desc>
\begin{code}
  data Con (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type₁
  data Desc (Γ : Tel ⊤) (I : Type) : Type₁ where
    []   : Desc Γ I
    _∷_  : Con Γ ∅ I → Desc Γ I → Desc Γ I
\end{code}
%</sop-desc>

%<*sop-con>
\begin{code}
  data Con Γ V I where
    𝟙   : V ⊢ I → Con Γ V I
    ρ   : V ⊢ I → Con Γ V I → Con Γ V I
    σ   : (S : V ⊢ Type) → Con Γ (V ▷ S) I → Con Γ V I
\end{code}
%</sop-con>

%<*sop-intp>
\begin{code}
  ⟦_⟧C : Con Γ V I → (⟦ Γ & V ⟧tel → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
  ⟦ 𝟙 j    ⟧C X pv i = i ≡ (j pv)
  ⟦ ρ j C  ⟧C X pv i = X pv (j pv) × ⟦ C ⟧C X pv i
  ⟦ σ S C  ⟧C X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C (X ∘ map₂ proj₁) (p , v , s) i

  ⟦_⟧D : Desc Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
  ⟦ []      ⟧D X p i = ⊥
  ⟦ C ∷ Cs  ⟧D X p i = ⟦ C ⟧C (X ∘ proj₁) (p , tt) i  ⊎ ⟦ Cs ⟧D X p i
\end{code}
%</sop-intp>

%<*sop-mu>
\begin{code}
  data μ (D : Desc Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
    con : ⟦ D ⟧D (μ D) p i → μ D p i
\end{code}
%</sop-mu>

\begin{code}
module Orn where
  open Parameter

  private variable
    I J P : Type
    Γ Δ : Tel ⊤
    V W : ExTel Γ
    D E : Desc Γ I
    B C : Con Γ V I
\end{code}

%<*cxf>
\begin{code}
  Cxf : (Δ Γ : Tel P) → Type
  Cxf Δ Γ = ∀ {p} → ⟦ Δ ⟧tel p → ⟦ Γ ⟧tel p
  
  Cxf′ : Cxf Δ Γ → (W : ExTel Δ) (V : ExTel Γ) → Type
  Cxf′ g W V = ∀ {d} → ⟦ W ⟧tel d → ⟦ V ⟧tel (g d)

  over : {g : Cxf Δ Γ} → Cxf′ g W V → ⟦ Δ & W ⟧tel → ⟦ Γ & V ⟧tel
  over v (d , w) = _ , v w
\end{code}
%</cxf>

%<*orn-type>
\begin{code}
  data Orn  (g : Cxf Δ Γ) (i : J → I) :
            (D : Desc Γ I) (E : Desc Δ J) → Type
            
  data ConOrn (g : Cxf Δ Γ) (v : Cxf′ g W V) (i : J → I) :
              (B : Con Γ V I) (C : Con Δ W J) → Type
  
  data Orn g i where
    []   : Orn g i [] []
    _∷_  : ConOrn g id i B C → Orn g i D E → Orn g i (B ∷ D) (C ∷ E)  
\end{code}
%</orn-type>

%<*orn-forget-type>
\begin{code}
  ornForget  : ∀ {g i} → Orn g i D E
             → ∀ d j → μ E d j → μ D (g d) (i j) 
\end{code}
%</orn-forget-type>

%<*orn-forget-type>
\begin{code}
  pre₂ : {A B C X Y : Type} → (A → B → C) → (X → A) → (Y → B) → X → Y → C
  pre₂ f a b x y = f (a x) (b y)

  eraseCon  : {B : Con Γ V I} {C : Con Δ W J} → ∀ {g} {v : Cxf′ g W V} {i}
            → ConOrn g v i B C → {X : ⟦ Γ & V ⟧tel → I → Type}
            → ∀ d w j → ⟦ C ⟧C (pre₂ X (over v) i) (d , w) j → ⟦ B ⟧C X (g d , v w) (i j)
\end{code}
%</orn-forget-type>

\begin{code}
  data ConOrn g v i where
\end{code}

\begin{code}
    𝟙  : ∀ {vi wj}
       → (∀ d w → vi (g d , v w) ≡ i (wj (d , w)))
       → ConOrn g v i (𝟙 vi) (𝟙 wj)
\end{code}

\begin{code}
  eraseCon {i = i} (𝟙 p) d w j q = trans (cong i q) (sym (p d w)) 
\end{code}

\begin{code}
  eraseCon O = {!!}
\end{code}

\begin{code}
  ornForget O d j x = {!!}
\end{code}
