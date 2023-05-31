{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Orn where

open import Ornament.TypeInType.Informed


open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude using (cong; sym; refl; _∙_; subst; subst2)



private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ


-- ornaments
data Orn (f : Cxf Δ Γ) (e : K → J) : Desc Γ J → Desc Δ K → Type
ornForget : {f : Cxf Δ Γ} {e : K → J} {D : Desc Γ J} {E : Desc Δ K} → Orn f e D E → ∀ p {i} → μ E p i → μ D (f p) (e i)


data Orn f e where
ornForget = {!!}

data ConOrn {c : Cxf Δ Γ} (f : VxfO c W V) (e : K → J) : Con Γ J V → Con Δ K W → Type where
  -- preserving
  𝟙 : ∀ {k j}
    → (∀ p → e (k p) ≡ j (over f p)) 
    → ConOrn f e (𝟙 j) (𝟙 k)
  --  → ConOrn f e (𝟙 (e ∘ k)) (𝟙 (k ∘ f))
    
  ρ : ∀ {k j g h D E}
    → ConOrn f e D E
    → (∀ p → g (c p) ≡ c (h p))
    → (∀ p → e (k p) ≡ j (over f p)) 
    → ConOrn f e (ρ j g D) (ρ k h E)
  -- note, using (ρ (e ∘ k) ...) (ρ (k ∘ f) ...) here gives a nasty metavariable out of scope when writing ornaments later, for some reason

  σ : ∀ {S} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {g : Vxf Γ (V ▷ S) _} {h : Vxf Δ (W ▷ (S ∘ over f)) _}
    → (f' : VxfO c W' V')
    → ConOrn f' e D E
    → (∀ {p'} (p : ⟦ W ▷ (S ∘ over f) ⟧tel p') → g (VxfO-▷ f S p) ≡ f' (h p))
    → ConOrn f e (σ S g D) (σ (S ∘ over f) h E)
    
  δ : ∀ {R : Desc Θ L} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {j : Γ & V ⊢ L} {k} {g : Vxf Γ _ _} {h : Vxf Δ _ _} {f' : VxfO c _ _}
    → ConOrn f' e D E
    → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f) ⟧tel p') → g (VxfO-▷ f (liftM2 (μ R) k j) p) ≡ f' (h p))
    → ConOrn f e (δ j k R g D) (δ (j ∘ over f) (k ∘ over f) R h E)

  -- extending
  Δρ : ∀ {D : Con Γ J V} {E} {k} {h}
     → ConOrn f e D E
     → ConOrn f e D (ρ k h E) 
  -- ^ you might want to disable this if you want to preserve recursive structure

  Δσ : ∀ {W'} {S} {D : Con Γ J V} {E : Con Δ K W'}
     → (f' : VxfO c _ _) → {h : Vxf Δ _ _}
     → ConOrn f' e D E
     → (∀ {p'} (p : ⟦ W ▷ S ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → ConOrn f e D (σ S h E)

  Δδ : ∀ {W'} {R : Desc Θ L} {D : Con Γ J V} {E : Con Δ K W'} {f' : VxfO c _ _} {m} {k} {h : Vxf Δ _ _}
     → ConOrn f' e D E
     → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) m k ⟧tel p') → f (p .proj₁) ≡ f' (h p))
     → ConOrn f e D (δ k m R h E)

  -- fixing
  ∇σ : ∀ {S} {V'} {D : Con Γ J V'} {E : Con Δ K W} {g : Vxf Γ _ _}
     → (s : V ⊧ S)
     → ConOrn ((g ∘ ⊧-▷ s) ∘ f) e D E
     → ConOrn f e (σ S g D) E
     
  ∇δ : ∀ {R : Desc Θ L} {V'} {D : Con Γ J V'} {E : Con Δ K W} {m} {k} {g : Vxf Γ _ _}
     → (s : V ⊧ liftM2 (μ R) m k)
     → ConOrn ((g ∘ ⊧-▷ s) ∘ f) e D E
     → ConOrn f e (δ k m R g D) E

  -- composition
  ∙δ : ∀ {D : Con Γ J V} {W'} {E : Con Δ K W'} {c'} {f'' : VxfO c' W V} {e''} {R : Desc Θ L} {Λ} {M} {R' : Desc Λ M} {f' : Cxf Λ Θ} {e'} {m} {k} {h : Vxf Γ _ _} {g : Vxf Δ _ _}
     → ConOrn (f'' ∘ g) e'' D E
     → (O : Orn {Δ = Λ} {K = M} f' e' R R')
     → ConOrn f e (δ (e' ∘ m) (f' ∘ k) R h D) (δ (m ∘ over f'') (k ∘ over f'') R' {!!} E)

-- h ∘ map₂ (λ {x} → ornForget O (k (_ , x)))

-- {- diagrams

-- -- σ
-- https://q.uiver.app/#q=WzAsMTMsWzEsMSwiXFxHYW1tYSxWIl0sWzAsMSwiXFxEZWx0YSxXIl0sWzIsMSwiXFxtYXRocm17VHlwZX0iXSxbMCwwLCJKIl0sWzEsMCwiSSJdLFsxLDIsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMSwzLCJXXFxyaGQgKFNcXGNpcmMgZikiXSxbMiwzLCJXJyJdLFszLDIsIlxcR2FtbWEsVlxccmhkIFMiXSxbNCwyLCJcXEdhbW1hLFYnIl0sWzMsMywiXFxEZWx0YSxXXFxyaGQgKFNcXGNpcmMgZikiXSxbNCwzLCJcXERlbHRhLFcnIl0sWzEsMCwiZiJdLFswLDIsIlMiXSxbMyw0LCJlIl0sWzUsNiwiZyJdLFs3LDgsImgiXSxbOSwxMCwiXFxoYXR7Z30iXSxbMTEsMTIsIlxcaGF0e2h9Il0sWzEyLDEwLCJmJyIsMl0sWzExLDksImYgXFxyaGQgUyJdXQ==

-- -- Δσ
-- https://q.uiver.app/#q=WzAsOCxbMCwxLCJXIl0sWzAsMiwiVyciXSxbMiwyLCJcXERlbHRhLFcnXFxyaGQgUyJdLFszLDIsIlxcR2FtbWEsViJdLFs0LDIsIlxcRGVsdGEsVyJdLFsyLDAsIlxcRGVsdGEsIFcnIl0sWzQsMCwiXFxtYXRocm17VHlwZX0iXSxbMywzLCJcXERlbHRhLFdcXHJoZCAoUyBcXGNpcmMgRWgpIl0sWzAsMSwiaCJdLFs0LDMsImYiLDJdLFsyLDUsIlxcbWF0aHJte2ZvcmdldH0iXSxbMiwzLCJmJyJdLFs1LDYsIlMiLDJdLFs0LDYsIlMnPVNcXGNpcmMgRWgiLDJdLFs3LDIsIkVoXFxyaGQgUyJdLFs3LDQsIlxcbWF0aHJte2ZvcmdldH0iLDJdLFs0LDUsIkVoIiwxXV0=

-- -- ∇σ
-- https://q.uiver.app/#q=WzAsNixbMCwxLCJcXERlbHRhLFciXSxbMSwxLCJcXEdhbW1hLFYiXSxbMSwyLCJcXEdhbW1hLCBWJyJdLFsyLDEsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMiwwLCJWIl0sWzAsMSwiZiIsMl0sWzAsMiwiZiciLDJdLFszLDQsImciLDJdLFs1LDMsIlxccmhkIHMiLDJdXQ==

-- -- ∙δ
-- https://q.uiver.app/#q=WzAsMzIsWzAsMCwiRDpcXG1hdGhybXtDb259XFxHYW1tYSBKIFYiXSxbMSwwLCJFOlxcbWF0aHJte0Nvbn1cXERlbHRhIEsgVyJdLFswLDEsIlI6XFxtYXRocm17RGVzY31cXFRoZXRhIEwiXSxbMSwxLCJSJzpcXG1hdGhybXtEZXNjfVxcTGFtYmRhIE0iXSxbNywwLCJcXGRlbHRhIGZfXFxUaGV0YSBsUmdEIl0sWzgsMCwiXFxkZWx0YSBmX1xcTGFtYmRhIG0gUicgaEUiXSxbMiwyLCJcXERlbHRhIl0sWzMsMiwiXFxHYW1tYSJdLFsyLDMsIlxcTGFtYmRhIl0sWzMsMywiXFxUaGV0YSJdLFs0LDIsIlciXSxbNSwyLCJWIl0sWzQsMywiTSJdLFs1LDMsIkwiXSxbNiwyLCJLIl0sWzcsMiwiSiJdLFs2LDMsIk0iXSxbNywzLCJMIl0sWzQsNSwiXFxHYW1tYSxWIl0sWzUsNSwiXFxUaGV0YSJdLFs0LDYsIlxcR2FtbWEsViJdLFs1LDYsIkwiXSxbNiw1LCJcXERlbHRhLFciXSxbNyw1LCJcXExhbWJkYSJdLFs2LDYsIlxcRGVsdGEsVyJdLFs3LDYsIlIiXSxbOCw1LCJWXFxyaGRcXG11IFIiXSxbOSw1LCJWJyJdLFs4LDYsIldcXHJoZFxcbXUgUiciXSxbOSw2LCJXJyJdLFsxMCw1LCJXJyJdLFsxMSw1LCJWJyJdLFswLDEsIiIsMCx7ImxldmVsIjoyfV0sWzIsMywiIiwwLHsibGV2ZWwiOjJ9XSxbNCw1LCIiLDAseyJsZXZlbCI6Mn1dLFs2LDcsImMiXSxbOCw5LCJjJyJdLFsxMCwxMSwiZl9jIl0sWzEyLDEzLCJmX3tjJ30iXSxbMTQsMTUsImUiXSxbMTYsMTcsImUnIl0sWzE4LDE5LCJmX1xcVGhldGEiXSxbMjAsMjEsImwiXSxbMjIsMjMsImZfXFxMYW1iZGEiXSxbMjQsMjUsIm0iXSxbMjYsMjcsImciXSxbMjgsMjksImgiXSxbMzAsMzEsImZfe2MnfSciXV0=

-- https://q.uiver.app/#q=WzAsMjQsWzAsMCwiRDpcXG1hdGhybXtDb259XFxHYW1tYSBKIFYiXSxbMSwwLCJFOlxcbWF0aHJte0Nvbn1cXERlbHRhIEsgVyJdLFswLDEsIlI6XFxtYXRocm17RGVzY31cXFRoZXRhIEwiXSxbMSwxLCJSJzpcXG1hdGhybXtEZXNjfVxcTGFtYmRhIE0iXSxbNywwLCJcXGRlbHRhIGZfXFxUaGV0YSBsUmdEIl0sWzgsMCwiXFxkZWx0YSBmX1xcTGFtYmRhIG0gUicgaEUiXSxbMiwyLCJcXERlbHRhIl0sWzMsMiwiXFxHYW1tYSJdLFs0LDIsIlciXSxbNSwyLCJWIl0sWzQsMywiVyciXSxbNSwzLCJWJyJdLFs2LDIsIksiXSxbNywyLCJKIl0sWzQsNSwiXFxHYW1tYSxWIl0sWzQsNCwiXFxUaGV0YSJdLFs0LDYsIkwiXSxbNSw1LCJcXERlbHRhLFciXSxbNSw0LCJcXExhbWJkYSJdLFs1LDYsIk0iXSxbOCw1LCJWXFxyaGRcXG11IFIiXSxbOSw1LCJWJyJdLFs4LDYsIldcXHJoZFxcbXUgUiciXSxbOSw2LCJXJyJdLFswLDEsIiIsMCx7ImxldmVsIjoyfV0sWzIsMywiIiwwLHsibGV2ZWwiOjJ9XSxbNCw1LCIiLDAseyJsZXZlbCI6Mn1dLFs2LDcsImMiXSxbOCw5LCJmX2MiXSxbMTAsMTEsImZfe2MnfSJdLFsxMiwxMywiZSJdLFsxNCwxNSwiZl9cXFRoZXRhIl0sWzE3LDE4LCJmX1xcTGFtYmRhIl0sWzIwLDIxLCJnIl0sWzIyLDIzLCJoIl0sWzIzLDIxLCJmX3tjJ30nIl0sWzIyLDIwLCJmX2NcXHJoZCBcXG1hdGhybXtmb3JnZXR9IiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzE0LDE3LCJjLGZfYyIsMl0sWzE1LDE4LCJjJyJdLFsxNywxOSwibSJdLFsxNCwxNiwibCJdLFsxOSwxNiwiZSciXV0=


-- -}

-- data Orn f e where
--   []  : Orn f e [] []
--   _∷_ : ∀ {D E D' E'} → ConOrn {c = f} id e D' E' → Orn f e D E → Orn f e (D' ∷ D) (E' ∷ E)


-- pre₂ : (A → B → C) → (X → A) → (Y → B) → X → Y → C
-- pre₂ f a b x y = f (a x) (b y)

-- {-# TERMINATING #-}
-- erase : ∀ {D : Desc Γ J} {E : Desc Δ K} {f} {e} {X : Fun Γ J} → Orn f e D E → ∀ p k → ⟦ E ⟧ (pre₂ X f e) p k → ⟦ D ⟧ X (f p) (e k)
-- erase' : ∀ {V W} {X : Fun Γ J} {D' : Con Γ J V} {E' : Con Δ K W} {c : Cxf Δ Γ} {f : VxfO c _ _} {e} (O : ConOrn f e D' E') → ∀ p k → ⟦ E' ⟧ (pre₂ X c e) p k → ⟦ D' ⟧ X (over f p) (e k)

-- erase (O ∷ Os) p k (inj₁ x) = inj₁ (erase' O (p , tt) k x)
-- erase (O ∷ Os) p k (inj₂ y) = inj₂ (erase Os p k y)

-- erase' (𝟙 j) p k x = cong _ x ∙ j p
-- erase' {X = X} (ρ O q r) p k (x , y) = subst2 X (sym (q _)) (r _) x , erase' O p k y
-- erase' {X = X} {c = c} (σ {D = D} {h = h} f' O q) (p , v) k (s , x) = s , subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O (p , h (v , s)) k x)
-- erase' {X = X} {c = c} (δ {D = D} O q) (p , v) k (r , x) = r , subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _)) ) (erase' O _ k x)
-- erase' (Δρ O) (p , v) k (x , y) = erase' O _ k y
-- erase' {X = X} {c = c} (Δσ {D = D} f' O q) (p , v) k (x , y) = subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O _ k y)
-- erase' {X = X} {c = c} (Δδ {D = D} O q) (p , v) k (x , y) = subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O _ k y)
-- erase' (∇σ s O) (p , v) k x = s _ , erase' O _ k x
-- erase' (∇δ s O) (p , v) k x = s _ , erase' O _ k x
-- erase' (∙δ R O) p k (x , y) = erase' R p k (ornForget O _ x , y)

-- ornAlg : ∀ {D : Desc Γ J} {E : Desc Δ K} {f} {e} → Orn f e D E → ⟦ E ⟧ (λ p k → μ D (f p) (e k)) ⇶ λ p k → μ D (f p) (e k)
-- ornAlg O p k x = con (erase O p k x)

-- ornForget O p = fold (ornAlg O) p _

-- -- examples
-- module Ornaments where
--   open Descriptions
  
--   ListD : Desc (∅ ▷ const Type) ⊤
--   ListD = 𝟙 _
--         ∷ σ- (proj₂ ∘ proj₁) (ρ0 _ (𝟙 _))
--         ∷ []

--   NatD-ListD : Orn ! ! NatD ListD
--   NatD-ListD = 𝟙 (const refl)
--              ∷ Δσ _ (ρ (𝟙 (const refl)) (const refl) (const refl)) (const refl)
--              ∷ []

--   ListD-VecD : Orn id ! ListD VecD
--   ListD-VecD = 𝟙 (λ _ i → tt)
--              ∷ σ id (Δσ _ (ρ (𝟙 (const refl)) (λ p → refl) (const refl)) λ p → refl) (const refl)
--              ∷ []


-- data Tag′ : Type where
--   CT DT : Tag′

