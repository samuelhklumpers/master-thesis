{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.OrnDesc where

open import Ornament.TypeInType.Informed
open import Ornament.TypeInType.Orn


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
  If If′ : Info


data OrnDesc Δ (f : Cxf Δ Γ) (K : Type) (e : K → J) : Desc Γ J → Type
data ConOrnDesc {Γ} {Δ} {c : Cxf Δ Γ} {W} {V} {K} {J} (f : VxfO c W V) (e : K → J) : Con Γ J V → Type

toDesc : {f : Cxf Δ Γ} {e : K → J} {D : Desc Γ J} → OrnDesc Δ f K e D → Desc Δ K
toCon  : {c : Cxf Δ Γ} {f : VxfO c W V} {e : K → J} {D : Con Γ J V} → ConOrnDesc f e D → Con Δ K W
toOrn : {f : Cxf Δ Γ} {e : K → J} {D : Desc Γ J} (OD : OrnDesc Δ f K e D) → Orn f e D (toDesc OD)
toConOrn  : {c : Cxf Δ Γ} {f : VxfO c W V} {e : K → J} {D : Con Γ J V} (OD : ConOrnDesc f e D) → ConOrn f e D (toCon OD)

data ConOrnDesc {Γ} {Δ} {c} {W} {V} {K} {J} f e where
  𝟙 : ∀ {j} (k : Δ & W ⊢ K) → (∀ p → e (k p) ≡ j (over f p)) → ConOrnDesc f e (𝟙 j)
    
  ρ : ∀ {j g D} (k : Δ & W ⊢ K) (h : Cxf Δ Δ) 
    → ConOrnDesc f e D
    → (∀ p → g (c p) ≡ c (h p))
    → (∀ p → e (k p) ≡ j (over f p)) 
    → ConOrnDesc f e (ρ j g D)
    
  σ : ∀ S {V'} {W'} {D : Con Γ J V'} {g : Vxf Γ (V ▷ S) _} (h : Vxf Δ (W ▷ (S ∘ over f)) W')
    → (f' : VxfO c W' V')
    → ConOrnDesc f' e D
    → (∀ {p'} (p : ⟦ W ▷ (S ∘ over f) ⟧tel p') → g (VxfO-▷ f S p) ≡ f' (h p))
    → ConOrnDesc f e (σ S g D)

  δ : ∀ (R : Desc Θ L) {V'} {W'} {D : Con Γ J V'} (j : Γ & V ⊢ L) k {g : Vxf Γ _ _} (h : Vxf Δ (W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f)) W') {f' : VxfO c _ _}
    → ConOrnDesc f' e D
    → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f) ⟧tel p') → g (VxfO-▷ f (liftM2 (μ R) k j) p) ≡ f' (h p))
    --→ ConOrnDesc f e (δ j k R g D) (δ (j ∘ over f) (k ∘ over f) R h E)
    → ConOrnDesc f e (δ j k R g D)

  -- extending
  Δρ : ∀ {D : Con Γ J V} (k : Δ & W ⊢ K) (h : Cxf Δ Δ)
     → ConOrnDesc f e D
     → ConOrnDesc f e D

  Δσ : ∀ {W'} S {D : Con Γ J V}
     → (f' : VxfO c _ _) (h : Vxf Δ (W ▷ S) W')
     → ConOrnDesc f' e D
     → (∀ {p'} (p : ⟦ W ▷ S ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → ConOrnDesc f e D 

  Δδ : ∀ {W'} (R : Desc Θ L) {D : Con Γ J V} {f' : VxfO c _ _} (k : W ⊢ L) (m : W ⊢ ⟦ Θ ⟧tel tt) (h : Vxf Δ (W ▷ liftM2 (μ R) m k) W')
     → ConOrnDesc f' e D
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) m k ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → ConOrnDesc f e D 

  -- fixing
  ∇σ : ∀ {S} {V'} {D : Con Γ J V'} {g : Vxf Γ _ _}
     → (s : V ⊧ S)
     → ConOrnDesc ((g ∘ ⊧-▷ s) ∘ f) e D
     → ConOrnDesc f e (σ S g D)

  ∇δ : ∀ {R : Desc Θ L} {V'} {D : Con Γ J V'} {m} {k} {g : Vxf Γ _ _}
     → (s : V ⊧ liftM2 (μ R) m k)
     → ConOrnDesc ((g ∘ ⊧-▷ s) ∘ f) e D
     → ConOrnDesc f e (δ k m R g D)

  -- composition
  ∙δ : ∀ {Θ Λ M L W' V'} {D : Con Γ J V'} {R : Desc Θ L}
         {c' : Cxf Λ Θ} {e' : M → L} {f'' : VxfO c W' V'} {fΘ : V ⊢ ⟦ Θ ⟧tel tt} (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
         {l : V ⊢ L} (m : W ⊢ M) 
     → (DE : ConOrnDesc f'' e D)
     → (RR' : OrnDesc Λ c' M e' R)
     → {g : Vxf _ (V ▷ _) V'} (h : Vxf _ (W ▷ _) W')
     → (p₁ : ∀ q w → c' (fΛ (q , w)) ≡ fΘ (c q , f w))
     → (p₂ : ∀ q w → e' (m (q , w))  ≡ l (c q , f w))
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ (toDesc RR')) fΛ m ⟧tel p') → f'' (h p) ≡ g (VxfO-▷-map f (liftM2 (μ R) fΘ l) (liftM2 (μ (toDesc RR')) fΛ m) (λ q w x → subst2 (μ R) (p₁ _ _) (p₂ _ _) (ornForget (toOrn RR') (fΛ (q , w)) x)) p))
     → ConOrnDesc f e (δ l fΘ R g D)

{-
  ∙δ : ∀ {Θ Λ M L W' V'} {D : Con Γ J V'} {R : Desc Θ L} (R' : Desc Λ M)
         {c' : Cxf Λ Θ} {e' : M → L} {f'' : VxfO c W' V'} {fΘ : V ⊢ ⟦ Θ ⟧tel tt} (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
         {l : V ⊢ L} (m : W ⊢ M) {g : Vxf _ (V ▷ _) V'} {h : Vxf _ (W ▷ _) W'}
     → (DE : ConOrnDesc f'' e D)
     → (RR' : Orn c' e' R R')
     → (p₁ : ∀ q w → c' (fΛ (q , w)) ≡ fΘ (c q , f w))
     → (p₂ : ∀ q w → e' (m (q , w))  ≡ l (c q , f w))
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R') fΛ m ⟧tel p') → f'' (h p) ≡ g (VxfO-▷-map f (liftM2 (μ R) fΘ l) (liftM2 (μ R') fΛ m) (λ q w x → subst2 (μ R) (p₁ _ _) (p₂ _ _) (ornForget RR' (fΛ (q , w)) x)) p))
     --→ ConOrn f e (δ l fΘ R g D) (δ m fΛ R' h E)
     → ConOrnDesc f e (δ l fΘ R g D)


  ∙δ : ∀ {D : Con Γ J V} {W'} (R : Desc Θ L) {Λ} {M} {f' : Cxf Λ Θ} {e'} (f' : Cxf Λ Θ) (m : W ⊢ M) (k : W ⊢ ⟦ Λ ⟧tel tt) (h : Vxf Δ (W ▷ liftM2 (μ R) (f' ∘ k) (e' ∘ m)) W') E
     → ConOrn f e D (δ (e' ∘ m) (f' ∘ k) R h E)
     -- ehhh
     → (O : OrnDesc Λ f' M e' R)
     → ConOrnDesc f e D 
-}


data OrnDesc Γ f J e where
  []  : OrnDesc Γ f J e []
  _∷_ : ∀ {D D'} → ConOrnDesc {c = f} id e D' → OrnDesc Γ f J e D → OrnDesc Γ f J e (D' ∷ D)

toDesc []      = []
toDesc (C ∷ D) = toCon C ∷ toDesc D 

toCon (𝟙 k x) = 𝟙 k
toCon (ρ k h D x y) = ρ k h (toCon D)
toCon {f = f} (σ S h f' D x) = σ (S ∘ over f) h (toCon D)
toCon {f = f} (δ R j k h D x) = δ (j ∘ over f) (k ∘ over f) R h (toCon D)
toCon (Δρ k h D) = ρ k h (toCon D)
toCon (Δσ S f' h D x) = σ S h (toCon D)
toCon (Δδ R k m h D x) = δ k m R h (toCon D)
toCon (∇σ s D) = toCon D
toCon (∇δ s D) = toCon D
toCon (∙δ fΛ m D RR' h p₁ p₂ x) = δ m fΛ (toDesc RR') h (toCon D)

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
