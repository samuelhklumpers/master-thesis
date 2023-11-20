\begin{code}
{-# OPTIONS --type-in-type --cubical #-}

module Appendix.Intp where

open import Cubical.Foundations.Prelude renaming (I to ι) hiding (J; _▷_)
open import Cubical.Foundations.Function

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma renaming (I to ι)
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂)

private variable
  I J K : Type
  A B C X Y Z : Type
  P P′ : Type

infixr 5 _∷_
infixr 10 _▷_
infixr 0 _⇶_

id : {A : Type} → A → A
id x = x

_⇉_ : (X Y : A → Type) → Type
X ⇉ Y = ∀ a → X a → Y a

_⇶_ : (X Y : A → B → Type) → Type
X ⇶ Y = ∀ a b → X a b → Y a b

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)

! : {A : Type} → A → ⊤
! _ = tt

_∘₃_ : ∀ {X Y Z : A → B → Type} → X ⇶ Y → (∀ {a b} → Z a b → X a b) → Z ⇶ Y
(g ∘₃ f) a b x = g a b (f x)

data Tel (P : Type) : Type
⟦_⟧tel : (Γ : Tel P) → P → Type

_⊢_ : (Γ : Tel P) → Type → Type
Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A

data Tel P where
  ∅   : Tel P
  _▷_ : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P

⟦ ∅     ⟧tel p = ⊤
⟦ Γ ▷ S ⟧tel p = Σ (⟦ Γ ⟧tel p) (S ∘ (p ,_)) 

ExTel : Tel ⊤ → Type
ExTel Γ = Tel (⟦ Γ ⟧tel tt)

private variable
    Γ Δ Θ : Tel P
    U V W : ExTel Γ

_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p

_▷′_ : (Γ : Tel P) (S : Type) → Tel P
Γ ▷′ S = Γ ▷ λ _ → S

_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Vxf : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
Vxf f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)

var→par : {f : Cxf Γ Δ} → Vxf f V W → ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel
var→par g (p , v) = _ , g v

Vxf-▷ : ∀ {c : Cxf Γ Δ} (f : Vxf c V W) (S : W ⊢ Type) → Vxf c (V ▷ (S ∘ var→par f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v

Vxf-▷-map : {c : Cxf Γ Δ} (f : Vxf c V W) (S : W ⊢ Type) (T : V ⊢ Type) → (∀ p v → T (p , v) → S (c p , f v)) → Vxf c (V ▷ T) (W ▷ S)
Vxf-▷-map f S T m (v , t) = (f v , m _ v t)

&-▷ : ∀ {S} → (p : ⟦ Δ & W ⟧tel) → S p → ⟦ Δ & W ▷ S ⟧tel
&-▷ (p , v) s = p , v , s

⊧-▷ : ∀ {V : ExTel Γ} {S} → V ⊧ S → Vxf id V (V ▷ S)
⊧-▷ s v = v , s (_ , v)

mutual
  data Desc (Γ : Tel ⊤) (I : Type) : Type where
    []   : Desc Γ I
    _∷_  : Con Γ ∅ I → Desc Γ I → Desc Γ I
    
  data Con (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type where
    𝟙  :  (i : Γ & V ⊢ I) → Con Γ V I

    ρ  :  (g : Cxf Γ Γ) (i : Γ & V ⊢ I) (C : Con Γ V I)
       →  Con Γ V I

    σ  :  (S : V ⊢ Type)
          (w : Vxf id (V ▷ S) W) (C : Con Γ W I)
       →  Con Γ V I

    δ  :  (d : Γ & V ⊢ ⟦ Δ ⟧tel tt) (j : Γ & V ⊢ J) 
          (R : Desc Δ J) (C : Con Γ V I)
       →  Con Γ V I
\end{code}

--   ⟦ 𝟙 i′         ⟧C X pv          i = i ≡ i′ pv
--   ⟦ ρ g i′ D     ⟧C X pv@(p , v)  i = X (g p) (i′ pv) × ⟦ D ⟧C X pv i
--   ⟦ σ S w D      ⟧C X pv@(p , v)  i = Σ[ s ∈ S pv ] ⟦ D ⟧C X (p , w (v , s)) i
--   ⟦ δ d j R D    ⟧C X pv          i = Σ[ s ∈ μ R (d pv) (j pv) ] ⟦ D ⟧C X pv i

--   ⟦ []     ⟧D X p i = ⊥
--   ⟦ C ∷ D  ⟧D X p i = (⟦ C ⟧C X (p , tt) i) ⊎ (⟦ D ⟧D X p i)
%<*Intp>
\begin{code}
mutual
  data μ (D : Desc Γ I) (p : ⟦ Γ ⟧tel tt) : I → Type  where
    con : ∀ {i} → IntpD (μ D) p i D → μ D p i

  data IntpC  (X : ⟦ Γ ⟧tel tt → I → Type)
              (pv : ⟦ Γ & V ⟧tel) (i : I)
              : Con Γ V I → Type where
    𝟙-i : ∀ {i′}
        → i ≡ i′ pv → IntpC X pv i (𝟙 i′)

    ρ-i : ∀ {g i′ D}
        → X (g (pv .fst)) (i′ pv) → IntpC X pv i D
        → IntpC X pv i (ρ g i′ D)

    σ-i : ∀ {S D} {w : Vxf id (V ▷ S) W}
        → (s : S pv) → IntpC X (pv .fst , w (pv .snd , s)) i D
        → IntpC X pv i (σ S w D)

    δ-i : ∀ {d j D} {R : Desc Δ J}
        → (s : μ R (d pv) (j pv)) → IntpC X pv i D
        → IntpC X pv i (δ d j R D)

  data IntpD (X : ⟦ Γ ⟧tel tt → I → Type)
             (p : ⟦ Γ ⟧tel tt) (i : I)
             : Desc Γ I → Type where
    ∷-il  : ∀ {C D} → IntpC X (p , tt)  i C → IntpD X p i (C ∷ D) 
    ∷-ir  : ∀ {C D} → IntpD X  p        i D → IntpD X p i (C ∷ D)

⟦_⟧D : Desc Γ I → (⟦ Γ ⟧tel tt → I → Type) → ⟦ Γ ⟧tel tt → I → Type
⟦_⟧D = λ D X p i → IntpD X p i D

⟦_⟧C : Con Γ V I → (⟦ Γ ⟧tel tt → I → Type) → ⟦ Γ & V ⟧tel → I → Type
⟦_⟧C = λ C X pv i → IntpC X pv i C
\end{code}
%</Intp>


%<*fold-type>
\begin{code}
fold : ∀ {D : Desc Γ I} {X} → ⟦ D ⟧D X ⇶ X → μ D ⇶ X
\end{code}
%</fold-type>

%<*mapFold>
\begin{code}     
mapDesc : ∀ {D' : Desc Γ I} (D : Desc Γ I) {X}
        → ∀ p i  → ⟦ D' ⟧D X ⇶ X → ⟦ D ⟧D (μ D') p i → ⟦ D ⟧D X p i
        
mapCon : ∀ {D' : Desc Γ I} {V} (C : Con Γ V I) {X}
       → ∀ p i v → ⟦ D' ⟧D X ⇶ X → ⟦ C ⟧C (μ D') (p , v) i → ⟦ C ⟧C X (p , v) i

fold f p i (con x) = f p i (mapDesc _ p i f x)

mapDesc (C ∷ D) p i f (∷-il x) = ∷-il (mapCon C p i tt f x)
mapDesc (C ∷ D) p i f (∷-ir y) = ∷-ir (mapDesc D p i f y)

mapCon (𝟙 j)        p i v f
       (𝟙-i    x)     = 𝟙-i x
       
mapCon (ρ g j C)    p i v f
       (ρ-i r  x)     = ρ-i (fold f (g p) (j (p , v)) r) (mapCon C p i v f x)
       
mapCon (σ S w C)    p i v f
       (σ-i s  x)     = σ-i s (mapCon C p i (w (v , s)) f x)
       
mapCon (δ d j R C)  p i v f
       (δ-i r  x)     = δ-i r (mapCon C p i v f x)
\end{code}
%</mapFold>
