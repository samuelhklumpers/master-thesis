\begin{document}
\begin{code}
{-# OPTIONS --type-in-type --rewriting #-}
module Tex.Discussion where

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
open import Data.Empty
open import Data.Maybe
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding (J)


open import Ornament.Desc
open import Ornament.OrnDesc

private variable
    A B C P : Type
    I J K L M : Type
    Γ Δ Θ Λ : Tel P
    U V W : ExTel Γ
    V′ W′ : ExTel Δ

    If If′ If″ If‴ : Info

    D E : DescI If Γ I
    CD CE : ConI If Γ V I
\end{code}

%<*index-interpretation>
\begin{code}
_&_⊧_ : (Γ : Tel ⊤) (V I : ExTel Γ) → Type
Γ & V ⊧ I = (pv : ⟦ Γ & V ⟧tel) → ⟦ I ⟧tel (fst pv)
\end{code} 
%</index-interpretation>

\begin{code}
data _≅_ {A : Type} (x : A) : {B : Type} → B → Type where
   refl : x ≅ x

module _ (If : Info) (Γ : Tel ⊤) (V I : ExTel Γ) where
\end{code}

\begin{code}
  _∙_⊧_ : {Γ : Tel ⊤} (g : Cxf Γ Γ) (V : ExTel Γ) (I : ExTel Γ)  → Type  
  g ∙ V ⊧ I =
\end{code}
\begin{code}
    (pv : ⟦ _ & V ⟧tel) → ⟦ I ⟧tel (g (fst pv))
\end{code}
\begin{code}
  ρ′ :  (g : Cxf Γ Γ) → g ∙ V ⊧ I → 
\end{code}
\begin{code}
        ⊤
  ρ′ _ _ = tt

  module _ (Δ : Tel ⊤) (W J : ExTel Δ) (c : Cxf Δ Γ) (v : VxfO c W V) (reindex : ∀ p → ⟦ J ⟧tel p → ⟦ I ⟧tel (c p)) where
\end{code}

\begin{code}
    ρ″ :  {g : Cxf Γ Γ} (h : Cxf Δ Δ)
          {i′ : g ∙ V ⊧ I} (j′ : h ∙ W ⊧ J)
          → g ∘ c ∼ c ∘ h
          → (∀ pw → reindex (h (fst pw)) (j′ pw) ≅ i′ (over v pw))
\end{code}
i ∘ j′ ∼ i′ ∘ over v
\begin{code}
       → ⊤
    ρ″ _ _ _ _ = tt
\end{code}

\begin{code}
module δ′ where
  open Info

  {-# NON_COVERING #-}
  mutual -- hmmm
    {-# TERMINATING #-}
\end{code}
%<*Delta-Info>
\begin{code}
    Delta : Info
    Delta .σi {Γ = Γ} {V = V} S
      =  Maybe (
         Σ[ Δ ∈ Tel ⊤ ] Σ[ J ∈ Type ] Σ[ j ∈ Γ & V ⊢ J ]
         Σ[ g ∈ Γ & V ⊢ ⟦ Δ ⟧tel tt ] Σ[ D ∈ DescI Delta Δ J ]
         (∀ pv → S pv ≡ liftM2 (μ D) g j pv))
\end{code}
%</Delta-Info>

\begin{code}
open δ′

module ∇′ {If : Info} {If′ : Info} {c : Cxf Δ Γ}
                   {v : VxfO c W V} {i : J → I} where
  postulate
\end{code}

%<*nabla-sigma>
\begin{code}
    ∇σ  : ∀ {S} 
        → (s : W ⊧ (S ∘ over v)) {g : Vxf Γ _ V′}
        → ConOrnDesc If′ (g ∘ λ pw → v pw , s (_ , pw)) i CD
        → ∀ {if}
        → ConOrnDesc If′ v i {If} (σ S {if = if} g CD)
\end{code}
%</nabla-sigma>

\begin{code}
open ∇′

module ∙δ′ {If : Info} {If′ : Info} {c : Cxf Δ Γ}
                   {v : VxfO c W V} {i : J → I} where
\end{code}

%<*comp-delta-nabla-sigma>
\begin{code}
  ∙δ′  :  {CD : ConI Delta _ _ _} {R : DescI Delta Θ K} {c′ : Cxf Λ Θ}
          {k′ : M → K} {k : V ⊢ K}  {fΘ : V ⊢ ⟦ Θ ⟧tel tt}
          {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
          (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
       → (RR′ : OrnDesc Delta Λ c′ M k′ R)
         (h : Vxf _ (W ▷ liftM2 (μ (toDesc RR′)) fΛ m) W′)
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
       → (DE : ConOrnDesc Delta _ i CD)
       →  ConOrnDesc Delta v i
          (σ  (liftM2 (μ R) fΘ k)
              {if = just (_ , _ , k , fΘ , R , λ pv → refl)}
              g CD)
  ∙δ′  {Λ = Λ} {R = R}  m fΛ RR′ h p₁ p₂ DE
    =  OΔσ+  (liftM2 (μ (toDesc RR′)) fΛ m)
             {if′ = just (Λ , _ , m , fΛ , toDesc RR′ , λ pv → refl)}
    (  ∇σ  (λ { (p , w , r) →  subst₂  (μ R) (p₁ _ _) (p₂ _ _)
                               (ornForget RR′ (fΛ (p , w)) (m (p , w)) r) })
           DE)
\end{code}
%</comp-delta-nabla-sigma>
\end{document}
