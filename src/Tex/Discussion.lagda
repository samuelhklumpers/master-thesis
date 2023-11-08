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
open import Data.List
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

    Me Me′ Me″ Me‴ : Meta

    D E : DescI Me Γ I
    CD CE : ConI Me Γ V I
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

module _ (Me : Meta) (Γ : Tel ⊤) (V I : ExTel Γ) where
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

  module _ (Δ : Tel ⊤) (W J : ExTel Δ) (c : Cxf Δ Γ) (v : Vxf c W V) (re-index : ∀ p → ⟦ J ⟧tel p → ⟦ I ⟧tel (c p)) where
\end{code}

\begin{code}
    ρ″ :  {g : Cxf Γ Γ} (h : Cxf Δ Δ)
          {i′ : g ∙ V ⊧ I} (j′ : h ∙ W ⊧ J)
          → g ∘ c ∼ c ∘ h
          → (∀ pw → re-index (h (fst pw)) (j′ pw) ≅ i′ (var→par v pw))
\end{code}
\begin{code}
       → ⊤
    ρ″ _ _ _ _ = tt
\end{code}

\begin{code}
module δ′ where
  open Meta

  {-# NON_COVERING #-}
  mutual -- hmmm
    {-# TERMINATING #-}
\end{code}
%<*Delta-Meta>
\begin{code}
    Delta : Meta
    Delta .σi {Γ = Γ} {V = V} S
      =  Maybe (
         Σ[ Δ ∈ Tel ⊤ ] Σ[ J ∈ Type ] Σ[ j ∈ Γ & V ⊢ J ]
         Σ[ g ∈ Γ & V ⊢ ⟦ Δ ⟧tel tt ] Σ[ D ∈ DescI Delta Δ J ]
         (∀ pv → S pv ≡ liftM2 (μ D) g j pv))
\end{code}
%</Delta-Meta>

\begin{code}
open δ′

module ∇′ {Me : Meta} {Me′ : Meta} {c : Cxf Δ Γ}
                   {v : Vxf c W V} {i : J → I} where
  postulate
\end{code}

%<*nabla-sigma>
\begin{code}
    ∇σ  : ∀ {S} 
        → (s : W ⊧ (S ∘ var→par v)) {g : Vxf id _ V′}
        → ConOrnDesc Me′ (g ∘ λ pw → v pw , s (_ , pw)) i CD
        → ∀ {me}
        → ConOrnDesc Me′ v i {Me} (σ S {me = me} g CD)
\end{code}
%</nabla-sigma>

\begin{code}
open ∇′

module ∙δ′ {Me : Meta} {Me′ : Meta} {c : Cxf Δ Γ}
                   {v : Vxf c W V} {i : J → I} where
\end{code}

%<*comp-delta-nabla-sigma>
\begin{code}
  ∙δ′  :  {CD : ConI Delta _ _ _} {R : DescI Delta Θ K} {c′ : Cxf Λ Θ}
          {k′ : M → K} {k : V ⊢ K}  {fΘ : V ⊢ ⟦ Θ ⟧tel tt}
          {g : Vxf id (V ▷ liftM2 (μ R) fΘ k) V′}  
          (fΛ : W ⊢ ⟦ Λ ⟧tel tt) (m : W ⊢ M) 
       → (RR′ : OrnDesc Delta Λ c′ M k′ R)
         (h : Vxf id (W ▷ liftM2 (μ (toDesc RR′)) fΛ m) W′)
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
       → (DE : ConOrnDesc Delta _ i CD)
       →  ConOrnDesc Delta v i
          (σ  (liftM2 (μ R) fΘ k)
              {me = just (_ , _ , k , fΘ , R , λ pv → refl)}
              g CD)
  ∙δ′  {Λ = Λ} {R = R}  fΛ m RR′ h p₁ p₂ DE
    =  OΔσ+  (liftM2 (μ (toDesc RR′)) fΛ m)
             {me′ = just (Λ , _ , m , fΛ , toDesc RR′ , λ pv → refl)}
    (  ∇σ  (λ { (p , w , r) →  subst₂  (μ R) (p₁ _ _) (p₂ _ _)
                               (ornForget RR′ (fΛ (p , w)) (m (p , w)) r) })
           DE)
\end{code}
%</comp-delta-nabla-sigma>

%<*RoseTree>
\begin{code}
data RoseTree (A : Type) : Type where
  rose : A → List (RoseTree A) → RoseTree A
\end{code}
%</RoseTree>

%<*RoseTree2>
\begin{code}
data RoseTree′ (A : Type) : Type where
  nil  : A → RoseTree′ A                       
  cons : RoseTree′ A → RoseTree′ A → RoseTree′ A  
\end{code}
%</RoseTree2>
-- nil x       ↔ rose x []
-- cons rx ry  ↔ rose y (rx ∷ rys) where ry = rose y rys

%<*Iso>
\AgdaTarget{Iso}
\AgdaTarget{rightInv}
\AgdaTarget{leftInv}
\begin{code}
record _≃_ A B : Type where
  constructor iso
  field
    fun  : A → B
    inv  : B → A
    rightInv  : ∀ b → fun (inv b) ≡ b 
    leftInv   : ∀ a → inv (fun a) ≡ a
\end{code}
%</Iso>

\begin{code}
Rose-correct : (A : Type) → RoseTree A ≃ RoseTree′ A
Rose-correct A = iso to from ret sec
  where
  to : RoseTree A → RoseTree′ A
  to (rose x [])          = nil x
  to (rose x (rx ∷ rxs))  = cons (to rx) (to (rose x rxs))

  from : RoseTree′ A → RoseTree A
  from (nil x)       = rose x []
  from (cons rx ry)  with from ry
  ... | rose y rys   = rose y (from rx ∷ rys)

  ret : (b : RoseTree′ A) → to (from b) ≡ b
  ret (nil x)       = refl
  ret (cons rx ry)  with from ry in p
  ... | rose y rys = cong₂ cons (ret rx) (trans (cong to (sym p)) (ret ry) )

  sec : (a : RoseTree A) → from (to a) ≡ a
  sec (rose x [])          = refl
  sec (rose x (rx ∷ rxs))  with from (to (rose x rxs)) in p | sec (rose x rxs)
  ... | rose .x .rxs | refl = cong (rose x ∘ (_∷ rxs)) (sec rx)
\end{code}


%<*almost-RoseTree>
\begin{code}
RoseD : Desc (∅ ▷ λ _ → Type) ⊤
RoseD  = σ- (λ { ((_ , A) , _) → A })
       ( ρ (λ { (_ , A) → _ , List A}) !
       ( 𝟙 _))
       ∷ []
\end{code}
%</almost-RoseTree>
\end{document}
