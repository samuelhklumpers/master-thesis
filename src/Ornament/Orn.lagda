\begin{code}
    
{-# OPTIONS --type-in-type --with-K #-}


module Ornament.Orn where

open import Ornament.Desc


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

private variable
  If If′ If″ If‴ : Info
\end{code}

Ornaments
%<*Orn-type>
\begin{code}
data Orn  {If} {If′} (f : Cxf Δ Γ) (e : K → J)
          : DescI If Γ J → DescI If′ Δ K → Type
\end{code}
%</Orn-type>

%<*ornForget-type>
\begin{code}
ornForget : {f : Cxf Δ Γ} {e : K → J} {D : DescI If Γ J} {E : DescI If′ Δ K}
          → Orn f e D E → ∀ p {i} → μ E p i → μ D (f p) (e i)
\end{code}
%</ornForget-type>

All significant squares have diagrams below
%<*ConOrn-type>
\begin{code}
data ConOrn  {If} {If′} {c : Cxf Δ Γ} (f : VxfO c W V) (e : K → J)
             : ConI If Γ J V → ConI If′ Δ K W → Type where
\end{code}
%</ConOrn-type>

Preserving
%<*Orn-1>
\begin{code}
  𝟙  : ∀ {k j}
     → (∀ p → e (k p) ≡ j (over f p))
     → ∀ {if if′}
     → ConOrn f e (𝟙 {if = if} j) (𝟙 {if = if′} k)
\end{code}
%</Orn-1>
(*)

%<*Orn-rho>
\begin{code}
  ρ  : ∀ {k j g h D E}
     → ConOrn f e D E
     → (∀ p → g (c p) ≡ c (h p))
     → (∀ p → e (k p) ≡ j (over f p))
     → ∀ {if if′}
     → ConOrn f e (ρ {if = if} j g D) (ρ {if = if′} k h E)
\end{code}
%</Orn-rho>

%<*Orn-sigma-delta>
\begin{code}
  σ  : ∀  {S} {V'} {W'} {D : ConI If Γ J V'} {E : ConI If′ Δ K W'}
          {g : Vxf Γ (V ▷ S) _} {h : Vxf Δ (W ▷ (S ∘ over f)) _}
     → (f' : VxfO c W' V')
     → ConOrn f' e D E
     → (∀ {p'} (p : ⟦ W ▷ (S ∘ over f) ⟧tel p') → g (VxfO-▷ f S p) ≡ f' (h p))
     → ∀ {if if′}
     → ConOrn f e (σ S {if = if} g D) (σ (S ∘ over f) {if = if′} h E)
    
  δ  : ∀  {R : DescI If″ Θ L} {V'} {W'}
          {D : ConI If Γ J V'} {E : ConI If′ Δ K W'}
          {j : Γ & V ⊢ L} {k} {g : Vxf Γ _ _} {h : Vxf Δ _ _} {f' : VxfO c _ _}
     → ConOrn f' e D E
     → (  ∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) (k ∘ over f) (j ∘ over f) ⟧tel p')
          → g (VxfO-▷ f (liftM2 (μ R) k j) p) ≡ f' (h p))
     → ∀ {if if′}
     → ∀ {iff iff′}
     → ConOrn f e  (δ {if = if} {iff = iff} j k R g D)
                   (δ {if = if′} {iff = iff′} (j ∘ over f) (k ∘ over f) R h E)
\end{code}
%</Orn-sigma-delta>

Extending
%<*Orn-+-rho>
\begin{code}
  Δρ  : ∀ {D : ConI If Γ J V} {E} {k} {h}
      → ConOrn f e D E
      → ∀ {if}
      → ConOrn f e D (ρ {if = if} k h E) 
\end{code}
%</Orn-+-rho>

%<*Orn-+-sigma-delta>
\begin{code}
  Δσ  : ∀ {W'} {S} {D : ConI If Γ J V} {E : ConI If′ Δ K W'}
      → (f' : VxfO c _ _) → {h : Vxf Δ _ _}
      → ConOrn f' e D E
      → (∀ {p'} (p : ⟦ W ▷ S ⟧tel p') → f (p .proj₁) ≡ f' (h p))
      → ∀ {if′}
      → ConOrn f e D (σ S {if = if′} h E)
 
  Δδ  : ∀  {W'} {R : DescI If″ Θ L} {D : ConI If Γ J V} {E : ConI If′ Δ K W'}
           {f' : VxfO c _ _} {m} {k} {h : Vxf Δ _ _}
      → ConOrn f' e D E
      → (∀ {p'} (p : ⟦ W ▷ liftM2 (μ R) m k ⟧tel p') → f (p .proj₁) ≡ f' (h p))
      → ∀ {if′ iff′}
      → ConOrn f e D (δ {if = if′} {iff = iff′} k m R h E)
\end{code}
%</Orn-+-sigma-delta>

Fixing
%<*Orn---sigma-delta>
\begin{code}
  ∇σ  : ∀ {S} {V'} {D : ConI If Γ J V'} {E : ConI If′ Δ K W} {g : Vxf Γ _ _}
      → (s : V ⊧ S)
      → ConOrn ((g ∘ ⊧-▷ s) ∘ f) e D E
      → ∀ {if}
      → ConOrn f e (σ S {if = if} g D) E
     
  ∇δ  : ∀  {R : DescI If″ Θ L} {V'} {D : ConI If Γ J V'} {E : ConI If′ Δ K W}
           {m} {k} {g : Vxf Γ _ _}
      → (s : V ⊧ liftM2 (μ R) m k)
      → ConOrn ((g ∘ ⊧-▷ s) ∘ f) e D E
      → ∀ {if iff}
      → ConOrn f e (δ {if = if} {iff = iff} k m R g D) E
\end{code}
%</Orn---sigma-delta>

Composition
%<*Orn-comp>
\begin{code}

  ∙δ  : ∀  {Θ Λ M L W' V'} {D : ConI If Γ J V'} {E : ConI If′ Δ K W'}
           {R : DescI If″ Θ L} {R' : DescI If‴ Λ M} {c' : Cxf Λ Θ} {e' : M → L}
           {f'' : VxfO c W' V'} {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {fΛ : W ⊢ ⟦ Λ ⟧tel tt}
           {l : V ⊢ L} {m : W ⊢ M} {g : Vxf _ (V ▷ _) V'} {h : Vxf _ (W ▷ _) W'}
      → ConOrn f'' e D E
      → (O : Orn c' e' R R')
      → (p₁ : ∀ q w → c' (fΛ (q , w)) ≡ fΘ (c q , f w))
      → (p₂ : ∀ q w → e' (m (q , w))  ≡ l (c q , f w))
      → ( ∀ {p'} (p : ⟦ W ▷ liftM2 (μ R') fΛ m ⟧tel p') →  f'' (h p) 
            ≡ g  (VxfO-▷-map f (liftM2 (μ R) fΘ l) (liftM2 (μ R') fΛ m)
                 (λ q w x →  subst2 (μ R) (p₁ _ _) (p₂ _ _)
                             (ornForget O (fΛ (q , w)) x)) p))
      → ∀ {if if′}
      → ∀ {iff iff′}
      → ConOrn f e  (δ {if = if}   {iff = iff}   l fΘ R   g D)
                    (δ {if = if′}  {iff = iff′}  m fΛ R'  h E) 
\end{code}
%</Orn-comp>

-- (*) https://q.uiver.app/#q=WzAsNCxbMCwwLCJcXGJ1bGxldCJdLFsxLDAsIlxcYnVsbGV0Il0sWzAsMSwiXFxidWxsZXQiXSxbMSwxLCJcXGJ1bGxldCJdLFswLDEsImUiXSxbMiwzLCJmIiwyXSxbMiwwLCJqIl0sWzMsMSwiaSIsMl0sWzMsMCwiayIsMV1d
-- note that having → ConOrn f e (𝟙 (e ∘ k)) (𝟙 (k ∘ f)) obviously satisfies the square
-- but if f is split epi, then the square also provides k.
-- f being split epi roughly states "Δ is a more informative parameter than Γ", so is this actually reasonable to ask?

{- diagrams
-- σ
https://q.uiver.app/#q=WzAsMTMsWzEsMSwiXFxHYW1tYSxWIl0sWzAsMSwiXFxEZWx0YSxXIl0sWzIsMSwiXFxtYXRocm17VHlwZX0iXSxbMCwwLCJKIl0sWzEsMCwiSSJdLFsxLDIsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMSwzLCJXXFxyaGQgKFNcXGNpcmMgZikiXSxbMiwzLCJXJyJdLFszLDIsIlxcR2FtbWEsVlxccmhkIFMiXSxbNCwyLCJcXEdhbW1hLFYnIl0sWzMsMywiXFxEZWx0YSxXXFxyaGQgKFNcXGNpcmMgZikiXSxbNCwzLCJcXERlbHRhLFcnIl0sWzEsMCwiZiJdLFswLDIsIlMiXSxbMyw0LCJlIl0sWzUsNiwiZyJdLFs3LDgsImgiXSxbOSwxMCwiXFxoYXR7Z30iXSxbMTEsMTIsIlxcaGF0e2h9Il0sWzEyLDEwLCJmJyIsMl0sWzExLDksImYgXFxyaGQgUyJdXQ==

-- Δσ
https://q.uiver.app/#q=WzAsOCxbMCwxLCJXIl0sWzAsMiwiVyciXSxbMiwyLCJcXERlbHRhLFcnXFxyaGQgUyJdLFszLDIsIlxcR2FtbWEsViJdLFs0LDIsIlxcRGVsdGEsVyJdLFsyLDAsIlxcRGVsdGEsIFcnIl0sWzQsMCwiXFxtYXRocm17VHlwZX0iXSxbMywzLCJcXERlbHRhLFdcXHJoZCAoUyBcXGNpcmMgRWgpIl0sWzAsMSwiaCJdLFs0LDMsImYiLDJdLFsyLDUsIlxcbWF0aHJte2ZvcmdldH0iXSxbMiwzLCJmJyJdLFs1LDYsIlMiLDJdLFs0LDYsIlMnPVNcXGNpcmMgRWgiLDJdLFs3LDIsIkVoXFxyaGQgUyJdLFs3LDQsIlxcbWF0aHJte2ZvcmdldH0iLDJdLFs0LDUsIkVoIiwxXV0=

-- ∇σ
https://q.uiver.app/#q=WzAsNixbMCwxLCJcXERlbHRhLFciXSxbMSwxLCJcXEdhbW1hLFYiXSxbMSwyLCJcXEdhbW1hLCBWJyJdLFsyLDEsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMiwwLCJWIl0sWzAsMSwiZiIsMl0sWzAsMiwiZiciLDJdLFszLDQsImciLDJdLFs1LDMsIlxccmhkIHMiLDJdXQ==

-- ∙δ
https://q.uiver.app/#q=WzAsMzIsWzAsMCwiRDpcXG1hdGhybXtDb259XFxHYW1tYSBKIFYiXSxbMSwwLCJFOlxcbWF0aHJte0Nvbn1cXERlbHRhIEsgVyJdLFswLDEsIlI6XFxtYXRocm17RGVzY31cXFRoZXRhIEwiXSxbMSwxLCJSJzpcXG1hdGhybXtEZXNjfVxcTGFtYmRhIE0iXSxbNywwLCJcXGRlbHRhIGZfXFxUaGV0YSBsUmdEIl0sWzgsMCwiXFxkZWx0YSBmX1xcTGFtYmRhIG0gUicgaEUiXSxbMiwyLCJcXERlbHRhIl0sWzMsMiwiXFxHYW1tYSJdLFsyLDMsIlxcTGFtYmRhIl0sWzMsMywiXFxUaGV0YSJdLFs0LDIsIlciXSxbNSwyLCJWIl0sWzQsMywiTSJdLFs1LDMsIkwiXSxbNiwyLCJLIl0sWzcsMiwiSiJdLFs2LDMsIk0iXSxbNywzLCJMIl0sWzQsNSwiXFxHYW1tYSxWIl0sWzUsNSwiXFxUaGV0YSJdLFs0LDYsIlxcR2FtbWEsViJdLFs1LDYsIkwiXSxbNiw1LCJcXERlbHRhLFciXSxbNyw1LCJcXExhbWJkYSJdLFs2LDYsIlxcRGVsdGEsVyJdLFs3LDYsIlIiXSxbOCw1LCJWXFxyaGRcXG11IFIiXSxbOSw1LCJWJyJdLFs4LDYsIldcXHJoZFxcbXUgUiciXSxbOSw2LCJXJyJdLFsxMCw1LCJXJyJdLFsxMSw1LCJWJyJdLFswLDEsIiIsMCx7ImxldmVsIjoyfV0sWzIsMywiIiwwLHsibGV2ZWwiOjJ9XSxbNCw1LCIiLDAseyJsZXZlbCI6Mn1dLFs2LDcsImMiXSxbOCw5LCJjJyJdLFsxMCwxMSwiZl9jIl0sWzEyLDEzLCJmX3tjJ30iXSxbMTQsMTUsImUiXSxbMTYsMTcsImUnIl0sWzE4LDE5LCJmX1xcVGhldGEiXSxbMjAsMjEsImwiXSxbMjIsMjMsImZfXFxMYW1iZGEiXSxbMjQsMjUsIm0iXSxbMjYsMjcsImciXSxbMjgsMjksImgiXSxbMzAsMzEsImZfe2MnfSciXV0=

https://q.uiver.app/#q=WzAsMjYsWzAsMCwiRDpcXG1hdGhybXtDb259XFxHYW1tYSBKIFYnIl0sWzEsMCwiRTpcXG1hdGhybXtDb259XFxEZWx0YSBLIFcnIl0sWzAsMSwiUjpcXG1hdGhybXtEZXNjfVxcVGhldGEgTCJdLFsxLDEsIlInOlxcbWF0aHJte0Rlc2N9XFxMYW1iZGEgTSJdLFs3LDAsIlxcZGVsdGEgZl9cXFRoZXRhIGxSZ0QiXSxbOCwwLCJcXGRlbHRhIGZfXFxMYW1iZGEgbSBSJyBoRSJdLFsyLDIsIlxcRGVsdGEiXSxbMywyLCJcXEdhbW1hIl0sWzQsMiwiVyJdLFs1LDIsIlYiXSxbNCwzLCJXJyJdLFs1LDMsIlYnIl0sWzYsMiwiSyJdLFs3LDIsIkoiXSxbMiw1LCJcXEdhbW1hLFYiXSxbMiw0LCJcXFRoZXRhIl0sWzIsNiwiTCJdLFs1LDUsIlxcRGVsdGEsVyJdLFs1LDQsIlxcTGFtYmRhIl0sWzUsNiwiTSJdLFs4LDUsIlZcXHJoZFxcbXUgUiJdLFs5LDUsIlYnIl0sWzgsNiwiV1xccmhkXFxtdSBSJyJdLFs5LDYsIlcnIl0sWzMsNSwiXFxHYW1tYSxWJyJdLFs0LDUsIlxcRGVsdGEsIFcnIl0sWzAsMSwiIiwwLHsibGV2ZWwiOjJ9XSxbMiwzLCIiLDAseyJsZXZlbCI6Mn1dLFs0LDUsIiIsMCx7ImxldmVsIjoyfV0sWzYsNywiYyJdLFs4LDksImYiXSxbMTAsMTEsImYnJyJdLFsxMiwxMywiZSJdLFsxNCwxNSwiZl9cXFRoZXRhIl0sWzE3LDE4LCJmX1xcTGFtYmRhIl0sWzIwLDIxLCJnIl0sWzIyLDIzLCJoIl0sWzIzLDIxLCJmJyciXSxbMjIsMjAsImZcXHJoZCBcXG1hdGhybXtmb3JnZXR9IiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzE4LDE1LCJjJyIsMl0sWzE3LDE5LCJtIl0sWzE0LDE2LCJsIl0sWzE5LDE2LCJlJyJdLFsyNSwyNCwiYyxmJyciXV0=
-}

%<*Orn>
\begin{code}
data Orn f e where
  []   : Orn f e [] []
  _∷_  : ∀ {D E D' E'}
       → ConOrn {c = f} id e D' E'
       → Orn f e D E
       → Orn f e (D' ∷ D) (E' ∷ E)
\end{code}
%</Orn>


%<*erase-type>
\begin{code}
pre₂ : (A → B → C) → (X → A) → (Y → B) → X → Y → C
pre₂ f a b x y = f (a x) (b y)

erase  : ∀ {D : DescI If Γ J} {E : DescI If′ Δ K} {f} {e} {X : PIType Γ J}
       → Orn f e D E → ∀ p k → ⟦ E ⟧ (pre₂ X f e) p k → ⟦ D ⟧ X (f p) (e k)
\end{code}
%</erase-type>

\begin{code}
erase' : ∀ {V W} {X : PIType Γ J} {D' : ConI If Γ J V} {E' : ConI If′ Δ K W} {c : Cxf Δ Γ} {f : VxfO c _ _} {e} (O : ConOrn f e D' E') → ∀ p k → ⟦ E' ⟧ (pre₂ X c e) p k → ⟦ D' ⟧ X (over f p) (e k)

erase (O ∷ Os) p k (inj₁ x) = inj₁ (erase' O (p , tt) k x)
erase (O ∷ Os) p k (inj₂ y) = inj₂ (erase Os p k y)

erase' (𝟙 j) p k x = cong _ x ∙ j p
erase' {X = X} (ρ O q r) p k (x , y) = subst2 X (sym (q _)) (r _) x , erase' O p k y
erase' {X = X} {c = c} (σ {D = D} {h = h} f' O q) (p , v) k (s , x) = s , subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O (p , h (v , s)) k x)
erase' {X = X} {c = c} (δ {D = D} O q) (p , v) k (r , x) = r , subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _)) ) (erase' O _ k x)
erase' (Δρ O) (p , v) k (x , y) = erase' O _ k y
erase' {X = X} {c = c} (Δσ {D = D} f' O q) (p , v) k (x , y) = subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O _ k y)
erase' {X = X} {c = c} (Δδ {D = D} O q) (p , v) k (x , y) = subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (sym (q _))) (erase' O _ k y)
erase' (∇σ s O) (p , v) k x = s _ , erase' O _ k x
erase' (∇δ s O) (p , v) k x = s _ , erase' O _ k x
erase' {X = X} {c = c} (∙δ {D = D} DE RR' p₁ p₂ p₃) (p , v) k (x , y) = subst2 (μ _) (p₁ _ _) (p₂ _ _) (ornForget RR' _ x) , subst (λ z → ⟦ D ⟧ X z _) (cong (c p ,_) (p₃ _)) (erase' DE _ _ y)
\end{code}

%<*ornAlg>
\begin{code}
ornAlg  : ∀ {D : DescI If Γ J} {E : DescI If′ Δ K} {f} {e}
        → Orn f e D E
        → ⟦ E ⟧ (λ p k → μ D (f p) (e k)) ⇶ λ p k → μ D (f p) (e k)
ornAlg O p k x = con (erase O p k x)
\end{code}
%</ornAlg>

%<*ornForget>
\begin{code}
ornForget O p = fold (ornAlg O) p _
\end{code}
%</ornForget>

Examples
\begin{code}
module Ornaments where
  open Descriptions
\end{code}

%<*NatD-ListD>
\begin{code}
  NatD-ListD  : Orn ! id NatD ListD
  NatD-ListD  = 𝟙 (const refl)
              ∷  Δσ _
              (  ρ (𝟙 (const refl)) (const refl) (const refl))
              (const refl)
              ∷ []
\end{code}
%</NatD-ListD>

%<*ListD-VecD>
\begin{code}
  ListD-VecD  : Orn id ! ListD VecD
  ListD-VecD  = 𝟙 (const refl)
              ∷  σ id
              (  Δσ _
              (  ρ (𝟙 (const refl)) (λ p → refl) (const refl))
              λ p → refl)
              (const refl)
              ∷ []
\end{code}
%</ListD-VecD>

\begin{code}
data Tag′ : Type where
  CT DT : Tag′
\end{code}
