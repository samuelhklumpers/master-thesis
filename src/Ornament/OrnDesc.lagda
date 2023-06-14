\begin{code}
{-# OPTIONS --type-in-type --with-K #-}


module Ornament.OrnDesc where

open import Ornament.Desc
open import Ornament.Orn


open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; refl; subst) renaming (trans to _∙_; subst₂ to subst2)


private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ
  If If′ If″ If‴ : Info


data OrnDesc {If} (If′ : Info) Δ (f : Cxf Δ Γ) (K : Type) (e : K → J) : DescI If Γ J → Type
\end{code}

%<*ConOrnDesc-type>
\begin{code}
data ConOrnDesc  {If} (If′ : Info) {Γ} {Δ} {c : Cxf Δ Γ}
                 {W} {V} {K} {J} (f : VxfO c W V) (e : K → J)
                 : ConI If Γ J V → Type
\end{code}
%</ConOrnDesc-type>

%<*toDesc>
\begin{code}
toDesc  : {f : Cxf Δ Γ} {e : K → J} {D : DescI If Γ J}
        → OrnDesc If′ Δ f K e D → DescI If′ Δ K

toCon   : {c : Cxf Δ Γ} {f : VxfO c W V} {e : K → J} {D : ConI If Γ J V}
        → ConOrnDesc If′ f e D → ConI If′ Δ K W
\end{code}
%</toDesc>

%<*toOrn>
\begin{code}
toOrn :  {f : Cxf Δ Γ} {e : K → J} {D : DescI If Γ J}
         (OD : OrnDesc If′ Δ f K e D) → Orn f e D (toDesc OD)

toConOrn :  {c : Cxf Δ Γ} {f : VxfO c W V} {e : K → J} {D : ConI If Γ J V}
            (OD : ConOrnDesc If′ f e D) → ConOrn f e D (toCon OD)
\end{code}
%</toOrn>

\begin{code}

data ConOrnDesc {If} If′ {Γ} {Δ} {c} {W} {V} {K} {J} f e where
\end{code}

%<*OrnDesc-1>
\begin{code}
  𝟙  : ∀ {j} (k : Δ & W ⊢ K)
     → (∀ p → e (k p) ≡ j (over f p))
     → ∀ {if} {if′ : If′ .𝟙i}
     → ConOrnDesc If′ f e (𝟙 {if = if} j)
\end{code}
%</OrnDesc-1>

\begin{code}
  ρ : ∀ {j g D} (k : Δ & W ⊢ K) (h : Cxf Δ Δ) 
    → ConOrnDesc If′ f e D
    → (∀ p → g (c p) ≡ c (h p))
    → (∀ p → e (k p) ≡ j (over f p))
    → ∀ {if} {if′ : If′ .ρi}
    → ConOrnDesc If′ f e (ρ {if = if} j g D)
    
  σ : ∀ S {V'} {W'} {D : ConI If Γ J V'} {g : Vxf Γ (V ▷ S) _} (h : Vxf Δ (W ▷ (S ∘ over f)) W')
    → (f' : VxfO c W' V')
    → ConOrnDesc If′ f' e D
    → (∀ {p'} (p : ⟦ W ▷ (S ∘ over f) ⟧tel p') → g (VxfO-▷ f S p) ≡ f' (h p))
    → ∀ {if} {if′ : If′ .σi (S ∘ over f)}
    → ConOrnDesc If′ f e (σ S {if = if} g D)

  δ : ∀ (R : DescI If″ Θ L) {V'} {W'} {D : ConI If Γ J V'} (j : Γ & V ⊢ L) k {g : Vxf Γ _ _} (h : Vxf Δ (W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f)) W') {f' : VxfO c _ _}
    → ConOrnDesc If′ f' e D
    → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f) ⟧tel p') → g (VxfO-▷ f (liftM2 (μ R) k j) p) ≡ f' (h p))
    → ∀ {if iff} {if′ : If′ .δi Θ L} {iff′ : InfoF If″ If′}
    → ConOrnDesc If′ f e (δ {if = if} {iff = iff} j k R g D)

  -- extending
  Δρ : ∀ {D : ConI If Γ J V} (k : Δ & W ⊢ K) (h : Cxf Δ Δ)
     → ConOrnDesc If′ f e D
     → {if′ : If′ .ρi}
     → ConOrnDesc If′ f e D

  Δσ : ∀ {W'} S {D : ConI If Γ J V}
     → (f' : VxfO c _ _) (h : Vxf Δ (W ▷ S) W')
     → ConOrnDesc If′ {W = W'} f' e D
     → (∀ {p'} (p : ⟦ W ▷ S ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → {if′ : If′ .σi S}
     → ConOrnDesc If′ f e D 

  Δδ : ∀ {W'} (R : DescI If″ Θ L) {D : ConI If Γ J V} {f' : VxfO c _ _} (k : W ⊢ L) (m : W ⊢ ⟦ Θ ⟧tel tt) (h : Vxf Δ (W ▷ liftM2 (μ R) m k) W')
     → ConOrnDesc If′ f' e D
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) m k ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → {if′ : If′ .δi Θ L} {iff′ : InfoF If″ If′}
     → ConOrnDesc If′ f e D 

  -- fixing
  ∇σ : ∀ {S} {V'} {D : ConI If Γ J V'} {g : Vxf Γ _ _}
     → (s : V ⊧ S)
     → ConOrnDesc If′ ((g ∘ ⊧-▷ s) ∘ f) e D
     → ∀ {if}
     → ConOrnDesc If′ f e (σ S {if = if} g D)

  ∇δ : ∀ {R : DescI If″ Θ L} {V'} {D : ConI If Γ J V'} {m} {k} {g : Vxf Γ _ _}
     → (s : V ⊧ liftM2 (μ R) m k)
     → ConOrnDesc If′ ((g ∘ ⊧-▷ s) ∘ f) e D
     → ∀ {if iff}
     → ConOrnDesc If′ f e (δ {if = if} {iff = iff} k m R g D)

  -- composition
  ∙δ : ∀ {Θ Λ M L W' V'} {D : ConI If Γ J V'} {R : DescI If″ Θ L}
         {c' : Cxf Λ Θ} {e' : M → L} {f'' : VxfO c W' V'} {fΘ : V ⊢ ⟦ Θ ⟧tel tt} (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
         {l : V ⊢ L} (m : W ⊢ M) 
     → (DE : ConOrnDesc If′ f'' e D)
     → (RR' : OrnDesc If‴ Λ c' M e' R)
     → {g : Vxf _ (V ▷ _) V'} (h : Vxf _ (W ▷ _) W')
     → (p₁ : ∀ q w → c' (fΛ (q , w)) ≡ fΘ (c q , f w))
     → (p₂ : ∀ q w → e' (m (q , w))  ≡ l (c q , f w))
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ (toDesc RR')) fΛ m ⟧tel p') → f'' (h p) ≡ g (VxfO-▷-map f (liftM2 (μ R) fΘ l) (liftM2 (μ (toDesc RR')) fΛ m) (λ q w x → subst2 (μ R) (p₁ _ _) (p₂ _ _) (ornForget (toOrn RR') (fΛ (q , w)) x)) p))
     → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
     → ConOrnDesc If′ f e (δ {if = if} {iff = iff} l fΘ R g D)



data OrnDesc If′ Γ f J e where
  []  : OrnDesc If′ Γ f J e []
  _∷_ : ∀ {D D'} → ConOrnDesc If′ {c = f} id e D' → OrnDesc If′ Γ f J e D → OrnDesc If′ Γ f J e (D' ∷ D)

toDesc []      = []
toDesc (C ∷ D) = toCon C ∷ toDesc D 

toCon (𝟙 k x {if′ = if}) = 𝟙 {if = if} k
toCon (ρ k h D x y {if′ = if}) = ρ {if = if} k h (toCon D)
toCon {f = f} (σ S h f' D x {if′ = if}) = σ (S ∘ over f) {if = if} h (toCon D)
toCon {f = f} (δ R j k h D x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} (j ∘ over f) (k ∘ over f) R h (toCon D)
toCon (Δρ k h D {if′ = if}) = ρ {if = if} k h (toCon D)
toCon (Δσ S f' h D x {if′ = if}) = σ S {if = if} h (toCon D)
toCon (Δδ R k m h D x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} k m R h (toCon D)
toCon (∇σ s D) = toCon D
toCon (∇δ s D) = toCon D
toCon (∙δ fΛ m D RR' h p₁ p₂ x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} m fΛ (toDesc RR') h (toCon D)

toOrn []      = []
toOrn (C ∷ D) = toConOrn C ∷ toOrn D 

toConOrn (𝟙 k x) = 𝟙 x
toConOrn (ρ k h D x y) = ρ (toConOrn D) x y
toConOrn (σ S h f' D x) = σ f' (toConOrn D) x
toConOrn (δ R j k h D x) = δ (toConOrn D) x
toConOrn (Δρ k h D) = Δρ (toConOrn D)
toConOrn (Δσ S f' h D x) = Δσ f' (toConOrn D) x
toConOrn (Δδ R k m h D x) = Δδ (toConOrn D) x
toConOrn (∇σ s D) = ∇σ s (toConOrn D)
toConOrn (∇δ s D) = ∇δ s (toConOrn D)
toConOrn (∙δ fΛ m D RR' h p₁ p₂ x) = ∙δ (toConOrn D) (toOrn RR') p₁ p₂ x
\end{code}


\begin{code}
algOrn : ∀ {J K} → (D : DescI If Γ J) → ⟦ D ⟧ (λ p i → K i) ⇶ (λ p i → K i) → OrnDesc Plain Γ id (Σ J K) proj₁ D
algOrn []       ϕ = []
algOrn (C ∷ D)  ϕ = algOrnC C {!!} ∷ algOrn D {!!}
  where
  algOrnC : ∀ {J} {K : J → Type} → (C : ConI If Γ J V) → ⟦ C ⟧ (λ p i → K i) ⇶ (λ p i → K i) → ConOrnDesc Plain {K = Σ J K} id proj₁ C
  algOrnC (𝟙 j) ϕ = 𝟙 (λ pv → j pv , ϕ pv (j pv) refl) λ p → refl
  algOrnC {K = K} (ρ j g C) ϕ = Δσ (λ pv → K (j pv)) proj₁ id (ρ (λ { (p , v , k) → j (p , v) , k } ) g {!algOrnC C!} {!!} {!!}) λ p → refl
  algOrnC (σ S h C) ϕ = σ S h id (algOrnC C λ a b x → ϕ {!!} b {!? !}) λ p → refl
  algOrnC (δ j g R h C) ϕ = {!!}

\end{code}
