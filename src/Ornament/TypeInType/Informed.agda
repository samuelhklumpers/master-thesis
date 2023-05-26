{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Informed where

open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
--open import Relation.Binary.PropositionalEquality hiding (J)


private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type


infixr 10 _∷_
infixr 10 _▷_


! : {A : Type} → A → ⊤
! _ = tt

-- telescopes
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

_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

_&_⊢_ : (Γ : Tel ⊤) (V : ExTel Γ) → Type → Type
Γ & V ⊢ A = ⟦ Γ & V ⟧tel → A

Fun : Tel ⊤ → Type → Type
Fun Γ J = ⟦ Γ ⟧tel tt → J → Type

private variable
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Exf : (Γ Δ : Tel ⊤) (V : ExTel Γ) (W : ExTel Δ) → Type
Exf Γ Δ V W = ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel

Vxf : (Γ : Tel ⊤) (V W : ExTel Γ) → Type
Vxf Γ V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel p

Cxf-Exf : Cxf Γ Δ → Exf Γ Δ ∅ ∅
Cxf-Exf f (p , _) = f p , _ 

Vxf-Exf : Vxf Γ V W → Exf Γ Γ V W
Vxf-Exf f (p , v) = p , f v

Vxf-▷ : (f : Vxf Γ V W) (S : Γ & W ⊢ Type) → Vxf Γ (V ▷ (S ∘ Vxf-Exf f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v

Exf-▷ : (f : Exf Γ Δ V W) (S : Δ & W ⊢ Type) → Exf Γ Δ (V ▷ (S ∘ f)) (W ▷ S)
Exf-▷ f S (p , v , s) = let (p' , v') = f (p , v) in p' , v' , s

&-drop-▷ : ∀ {S} → ⟦ Γ & V ▷ S ⟧tel → ⟦ Γ & V ⟧tel
&-drop-▷ (p , v , s) = p , v

par : ∀ {V : ExTel Γ} {p} → ⟦ V ⟧tel p → ⟦ Γ ⟧tel tt
par {p = p} _ = p

⊧-▷ : ∀ {V : ExTel Γ} {S} → V ⊧ S → Vxf Γ V (V ▷ S)
⊧-▷ s v = v , s (par v , v)

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)


-- descriptions
record Info : Type where
  field
    𝟙i : Type
    ρi : Type
    σi : ∀ {Γ V} → (S : Γ & V ⊢ Type) → Type
    δi : Type
    -- informed descriptions know who they are! we don't need to introduce ourselves twice, unlike newcomers like (S : Γ & V ⊢ Type)

open Info

Plain : Info
Plain .𝟙i = ⊤
Plain .ρi = ⊤
Plain .σi _ = ⊤
Plain .δi = ⊤

private variable
  If : Info

{-# NO_POSITIVITY_CHECK #-}
data DescI (If : Info) (Γ : Tel ⊤) (J : Type) : Type
data μ (D : DescI If Γ J) (p : ⟦ Γ ⟧tel tt) : J → Type
data ConI (If : Info) (Γ : Tel ⊤) (J : Type) (V : ExTel Γ) : Type where
  𝟙 : {if : If .𝟙i} → Γ & V ⊢ J → ConI If Γ J V
  ρ : {if : If .ρi} → Γ & V ⊢ J → Cxf Γ Γ → ConI If Γ J V → ConI If Γ J V
  σ : (S : Γ & V ⊢ Type) → {if : If .σi S} → Vxf Γ (V ▷ S) W → ConI If Γ J W → ConI If Γ J V
  δ : {if : If .δi} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If Δ K) → (h : Vxf Γ (V ▷ liftM2 (μ D) g j) W) → ConI If Γ J W → ConI If Γ J V

σ+ : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J (V ▷ S) → ConI If Γ J V
σ+ S {if = if} C = σ S {if = if} id C

σ- : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J V → ConI If Γ J V
σ- S {if = if} C = σ S {if = if} proj₁ C

δ+ : {if : If .δi} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If Δ K) → ConI If Γ J (V ▷ liftM2 (μ D) g j) → ConI If Γ J V
δ+ {if = if} j g R D = δ {if = if} j g R id D

δ- : {if : If .δi} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If Δ K) → ConI If Γ J V → ConI If Γ J V
δ- {if = if} j g R D = δ {if = if} j g R proj₁ D

ρ0 : {if : If .ρi} → Γ & V ⊢ J → ConI If Γ J V → ConI If Γ J V
ρ0 {if = if} r D = ρ {if = if} r id D


data DescI If Γ J where
  []  : DescI If Γ J
  _∷_ : ConI If Γ J ∅ → DescI If Γ J → DescI If Γ J 

Con = ConI Plain
Desc = DescI Plain

data Tag Γ : Type where
  CT : ExTel Γ → Tag Γ
  DT : Tag Γ

module _ {If : Info} where
  UnTag : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnTag Γ J (CT V) = ConI If Γ J V
  UnTag Γ J DT     = DescI If Γ J

  UnFun : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnFun Γ J (CT V) = ⟦ Γ & V ⟧tel → J → Type
  UnFun Γ J DT     = Fun Γ J


  -- interpretation
  ⟦_⟧ : {t : Tag Γ} → UnTag Γ J t → Fun Γ J → UnFun Γ J t
  ⟦_⟧ {t = CT V} (𝟙 j)         X pv i         = i ≡ j pv
  ⟦_⟧ {t = CT V} (ρ j f D)     X pv@(p , v) i = X (f p) (j pv) × ⟦ D ⟧ X pv i
  ⟦_⟧ {t = CT V} (σ S h D)     X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ D ⟧ X (p , h (v , s)) i
  ⟦_⟧ {t = CT V} (δ j g R h D) X pv@(p , v) i = Σ[ s ∈ μ R (g pv) (j pv) ] ⟦ D ⟧ X (p , h (v , s)) i
  ⟦_⟧ {t = DT}   []            X p i = ⊥
  ⟦_⟧ {t = DT}   (C ∷ D)       X p i = (⟦ C ⟧ X (p , tt) i) ⊎ (⟦ D ⟧ X p i) 


data μ D p where
  con : ∀ {i} → ⟦ D ⟧ (μ D) p i → μ D p i
  

-- examples
module Descriptions where
  NatD : Desc ∅ ⊤
  NatD = 𝟙 _
       ∷ ρ0 _ (𝟙 _)
       ∷ []

  VecD : Desc (∅ ▷ const Type) ℕ
  VecD = 𝟙 (const 0)
       ∷ σ- (proj₂ ∘ proj₁) (σ+ (const ℕ) (ρ0 (proj₂ ∘ proj₂) (𝟙 (suc ∘ proj₂ ∘ proj₂))))
       ∷ []

  DigitD : Desc (∅ ▷ const Type) ⊤
  DigitD = σ- (proj₂ ∘ proj₁) (𝟙 _)
         ∷ σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (𝟙 _))
         ∷ σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (𝟙 _)))
         ∷ []
         
  data Node (A : Type) : Type where
    two   : A → A     → Node A
    three : A → A → A → Node A

  FingerD : Desc (∅ ▷ const Type) ⊤
  FingerD = 𝟙 _
          ∷ σ- (proj₂ ∘ proj₁) (𝟙 _)
          ∷ δ- _ proj₁ DigitD (ρ _ (λ { (_ , A) → (_ , Node A) }) (δ- _ proj₁ DigitD (𝟙 _)))
          ∷ []


-- ornaments
data Orn (f : Cxf Δ Γ) (e : K → J) : Desc Γ J → Desc Δ K → Type
ornForget : {f : Cxf Δ Γ} {e : K → J} {D : Desc Γ J} {E : Desc Δ K} → Orn f e D E → ∀ p {i} → μ E p i → μ D (f p) (e i)  
data ConOrn (f : Exf Δ Γ W V) (e : K → J) : Con Γ J V → Con Δ K W → Type where
  -- preserving
  𝟙 : ∀ {k j}
    → (∀ p → e (k p) ≡ j (f p)) 
    → ConOrn f e (𝟙 j) (𝟙 k)
  --  → ConOrn f e (𝟙 (e ∘ k)) (𝟙 (k ∘ f))
    
  ρ : ∀ {k j g h D E}
    → ConOrn f e D E
    → Σ[ m ∈ Cxf Δ Γ ] (∀ p → g (m p) ≡ m (h p))
    → (∀ p → e (k p) ≡ j (f p)) 
    → ConOrn f e (ρ j g D) (ρ k h E)
  -- (*1) note, using (ρ (e ∘ k) ...) (ρ (k ∘ f) ...) here gives a nasty metavariable out of scope when writing ornaments later, for some reason

  σ : ∀ {S} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {g : Vxf Γ _ _} {h : Vxf Δ _ _}
    → ∀ f'
    → ConOrn f' e D E
    → (∀ p → Vxf-Exf g (Exf-▷ f S p) ≡ f' (Vxf-Exf h p))
    → ConOrn f e (σ S g D) (σ (S ∘ f) h E)
    
  δ : ∀ {R : Desc Θ L} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {j : Γ & V ⊢ L} {k} {g : Vxf Γ _ _} {h : Vxf Δ _ _} {f'}
    → ConOrn f' e D E
    → (∀ p → Vxf-Exf g (Exf-▷ f _ p) ≡ f' (Vxf-Exf h p))
    → ConOrn f e (δ j k R g D) (δ (j ∘ f) (k ∘ f) R h E)

  -- extending
  Δρ : ∀ {D : Con Γ J V} {E} {k} {h}
     → ConOrn f e D E
     → ConOrn f e D (ρ k h E) 
  -- ^ you might want to disable this if you want to preserve recursive structure

  Δσ : ∀ {W'} {S} {D : Con Γ J V} {E : Con Δ K W'}
     → ∀ f' → {h : Vxf Δ _ _}
     → ConOrn f' e D E
     → (∀ p → f (&-drop-▷ p) ≡ f' (Vxf-Exf h p))
     → ConOrn f e D (σ S h E)

  Δδ : ∀ {W'} {R : Desc Θ L} {D : Con Γ J V} {E : Con Δ K W'} {f'} {m} {k} {h : Vxf Δ _ _}
     → ConOrn f' e D E
     → (∀ p → f (&-drop-▷ p) ≡ f' (Vxf-Exf h p))
     → ConOrn f e D (δ k m R h E)

  -- fixing
  ∇σ : ∀ {S} {V'} {D : Con Γ J V'} {E : Con Δ K W} {g : Vxf Γ _ _}
     → (s : V ⊧ S)
     → ConOrn (Vxf-Exf (g ∘ ⊧-▷ s) ∘ f) e D E
     → ConOrn f e (σ S g D) E
     
  ∇δ : ∀ {R : Desc Θ L} {V'} {D : Con Γ J V'} {E : Con Δ K W} {m} {k} {g : Vxf Γ _ _}
     → (s : V ⊧ _)
     → ConOrn (Vxf-Exf (g ∘ ⊧-▷ s) ∘ f) e D E
     → ConOrn f e (δ k m R g D) E

  -- composition
  ∙δ : ∀ {D : Con Γ J V} {W'} {R : Desc Θ L} {Λ} {M} {R' : Desc Λ M} {R'} {f' : Cxf Λ Θ} {e'} {E : Con Δ K W'} {f'} {m} {k} {h : Vxf Δ _ _}
     → ConOrn f e D (δ (e' ∘ m) (f' ∘ k) R h E)
     → (O : Orn {Δ = Λ} {K = M} f' e' R R')
     → ConOrn f e D (δ m k R' (h ∘ map₂ (λ {x} → ornForget O (k (par x , x)))) E)
     --                            ^ shove this into a corner where nobody will ever find it
     -- also this will probably end your life if you try to get any decently complicated h, similarly to (*1)

-- 𝟙 : ∀ {i j} → (∀ p → e (j p) ≡ i (f p)) → ConOrn f e (𝟙 i) (𝟙 j)

{- diagrams

-- σ
https://q.uiver.app/#q=WzAsMTMsWzEsMSwiXFxHYW1tYSxWIl0sWzAsMSwiXFxEZWx0YSxXIl0sWzIsMSwiXFxtYXRocm17VHlwZX0iXSxbMCwwLCJKIl0sWzEsMCwiSSJdLFsxLDIsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMSwzLCJXXFxyaGQgKFNcXGNpcmMgZikiXSxbMiwzLCJXJyJdLFszLDIsIlxcR2FtbWEsVlxccmhkIFMiXSxbNCwyLCJcXEdhbW1hLFYnIl0sWzMsMywiXFxEZWx0YSxXXFxyaGQgKFNcXGNpcmMgZikiXSxbNCwzLCJcXERlbHRhLFcnIl0sWzEsMCwiZiJdLFswLDIsIlMiXSxbMyw0LCJlIl0sWzUsNiwiZyJdLFs3LDgsImgiXSxbOSwxMCwiXFxoYXR7Z30iXSxbMTEsMTIsIlxcaGF0e2h9Il0sWzEyLDEwLCJmJyIsMl0sWzExLDksImYgXFxyaGQgUyJdXQ==

-- Δσ
https://q.uiver.app/#q=WzAsOCxbMCwxLCJXIl0sWzAsMiwiVyciXSxbMiwyLCJcXERlbHRhLFcnXFxyaGQgUyJdLFszLDIsIlxcR2FtbWEsViJdLFs0LDIsIlxcRGVsdGEsVyJdLFsyLDAsIlxcRGVsdGEsIFcnIl0sWzQsMCwiXFxtYXRocm17VHlwZX0iXSxbMywzLCJcXERlbHRhLFdcXHJoZCAoUyBcXGNpcmMgRWgpIl0sWzAsMSwiaCJdLFs0LDMsImYiLDJdLFsyLDUsIlxcbWF0aHJte2ZvcmdldH0iXSxbMiwzLCJmJyJdLFs1LDYsIlMiLDJdLFs0LDYsIlMnPVNcXGNpcmMgRWgiLDJdLFs3LDIsIkVoXFxyaGQgUyJdLFs3LDQsIlxcbWF0aHJte2ZvcmdldH0iLDJdLFs0LDUsIkVoIiwxXV0=

-- ∇σ
https://q.uiver.app/#q=WzAsNixbMCwxLCJcXERlbHRhLFciXSxbMSwxLCJcXEdhbW1hLFYiXSxbMSwyLCJcXEdhbW1hLCBWJyJdLFsyLDEsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMiwwLCJWIl0sWzAsMSwiZiIsMl0sWzAsMiwiZiciLDJdLFszLDQsImciLDJdLFs1LDMsIlxccmhkIHMiLDJdXQ==

-}

data Orn f e where
  []  : Orn f e [] []
  _∷_ : ∀ {D E D' E'} → ConOrn (Cxf-Exf f) e D' E' → Orn f e D E → Orn f e (D' ∷ D) (E' ∷ E)

-- not again (should probably define fold at some point)
ornForget D p x = {!!}

-- examples
module Ornaments where
  open Descriptions
  
  ListD : Desc (∅ ▷ const Type) ⊤
  ListD = 𝟙 _
        ∷ σ- (proj₂ ∘ proj₁) (ρ0 _ (𝟙 _))
        ∷ []

  NatD-ListD : Orn ! ! NatD ListD
  NatD-ListD = 𝟙 (λ _ i → tt)
             ∷ Δσ (const _) (ρ (𝟙 λ _ i → tt) (! , const (λ i → _)) (const (λ i → _))) (const (λ i → _))
             ∷ []

  ListD-VecD : Orn id ! ListD VecD
  ListD-VecD = 𝟙 (λ _ i → tt)
             ∷ σ id (Δσ (λ { (p , v) → (p , _) }) (ρ (𝟙 (λ _ i → tt)) (id , (λ p i → p)) (λ _ i → tt)) λ { (q , tt , p) → λ i → (q , tt) }) (λ p → (λ i → p .proj₁ , tt))
             ∷ []

module Numbers where
  data Op : Type where
    ⊕ ⊛ : Op

  Number : Info
  Number .𝟙i = ℕ
  Number .ρi = Op
  Number .σi S = Op × ∀ p → S p → ℕ
  Number .δi = Op

  NatND : DescI Number ∅ ⊤
  NatND = 𝟙 {if = 0} _
        ∷ ρ0 {if = ⊕} _ (𝟙 {if = 1} _)
        ∷ []
