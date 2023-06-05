{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Desc where

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


infixr 10 _∷_
infixr 10 _▷_



_⇉_ : (X Y : A → Set) → Set
X ⇉ Y = ∀ a → X a → Y a

_⇶_ : (X Y : A → B → Set) → Set
X ⇶ Y = ∀ a b → X a b → Y a b

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)

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

VxfO : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
VxfO f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)

over : {f : Cxf Γ Δ} → VxfO f V W → Exf Γ Δ V W
over g (p , v) = _ , g v

Cxf-Exf : Cxf Γ Δ → Exf Γ Δ ∅ ∅
Cxf-Exf f (p , _) = f p , _ 

Vxf-Exf : Vxf Γ V W → Exf Γ Γ V W
Vxf-Exf f (p , v) = p , f v

Vxf-▷ : (f : Vxf Γ V W) (S : Γ & W ⊢ Type) → Vxf Γ (V ▷ (S ∘ Vxf-Exf f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v

VxfO-▷ : ∀ {c : Cxf Γ Δ} (f : VxfO c V W) (S : Δ & W ⊢ Type) → VxfO c (V ▷ (S ∘ over f)) (W ▷ S)
VxfO-▷ f S (p , v) = f p , v

VxfO-▷-map : {c : Cxf Γ Δ} (f : VxfO c V W) (S : W ⊢ Type) (T : V ⊢ Type) → (∀ p v → T (p , v) → S (c p , f v)) → VxfO c (V ▷ T) (W ▷ S)
VxfO-▷-map f S T m (v , t) = (f v , m _ v t)

Exf-▷ : (f : Exf Γ Δ V W) (S : Δ & W ⊢ Type) → Exf Γ Δ (V ▷ (S ∘ f)) (W ▷ S)
Exf-▷ f S (p , v , s) = let (p' , v') = f (p , v) in p' , v' , s

&-▷ : ∀ {S} → (p : ⟦ Δ & W ⟧tel) → S p → ⟦ Δ & W ▷ S ⟧tel
&-▷ (p , v) s = p , v , s

&-drop-▷ : ∀ {S} → ⟦ Γ & V ▷ S ⟧tel → ⟦ Γ & V ⟧tel
&-drop-▷ (p , v , s) = p , v

ExPar : ∀ {V : ExTel Γ} {p} → ⟦ V ⟧tel p → ⟦ Γ ⟧tel tt
ExPar {p = p} _ = p

⊧-▷ : ∀ {V : ExTel Γ} {S} → V ⊧ S → Vxf Γ V (V ▷ S)
⊧-▷ s v = v , s (ExPar v , v)


-- descriptions
record Info : Type where
  field
    𝟙i : Type
    ρi : Type
    σi : ∀ {Γ V} → (S : Γ & V ⊢ Type) → Type
    δi : Tel ⊤ → Type → Type
    -- informed descriptions know who they are! we don't need to introduce ourselves twice, unlike newcomers like (S : Γ & V ⊢ Type)

open Info public

record InfoF (L R : Info) : Type where
  field
    𝟙f : L .𝟙i → R .𝟙i
    ρf : L .ρi → R .ρi
    σf : {V : ExTel Γ} (S : V ⊢ Type) → L .σi S → R .σi S
    δf : ∀ Γ A → L .δi Γ A → R .δi Γ A

open InfoF public

_∘InfoF_ : ∀ {X Y Z} → InfoF Y Z → InfoF X Y → InfoF X Z
(ϕ ∘InfoF ψ) .𝟙f x = ϕ .𝟙f (ψ .𝟙f x)
(ϕ ∘InfoF ψ) .ρf x = ϕ .ρf (ψ .ρf x)
(ϕ ∘InfoF ψ) .σf S x = ϕ .σf S (ψ .σf S x)
(ϕ ∘InfoF ψ) .δf Γ A x = ϕ .δf Γ A (ψ .δf Γ A x)

Plain : Info
Plain .𝟙i = ⊤
Plain .ρi = ⊤
Plain .σi _ = ⊤
Plain .δi _ _ = ⊤

private variable
  If If′ : Info

data DescI (If : Info) (Γ : Tel ⊤) (J : Type) : Type
data μ (D : DescI If Γ J) (p : ⟦ Γ ⟧tel tt) : J → Type
data ConI (If : Info) (Γ : Tel ⊤) (J : Type) (V : ExTel Γ) : Type where
  𝟙 : {if : If .𝟙i} (j : Γ & V ⊢ J) → ConI If Γ J V
  ρ : {if : If .ρi} (j : Γ & V ⊢ J) (g : Cxf Γ Γ) (C : ConI If Γ J V) → ConI If Γ J V
  σ : (S : Γ & V ⊢ Type) {if : If .σi S} (h : Vxf Γ (V ▷ S) W) (C : ConI If Γ J W) → ConI If Γ J V
  δ : {if : If .δi Δ K} {iff : InfoF If′ If} (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (R : DescI If′ Δ K) (h : Vxf Γ (V ▷ liftM2 (μ R) g j) W) (C : ConI If Γ J W) → ConI If Γ J V

σ+ : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J (V ▷ S) → ConI If Γ J V
σ+ S {if = if} C = σ S {if = if} id C

σ- : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J V → ConI If Γ J V
σ- S {if = if} C = σ S {if = if} proj₁ C

δ+ : {if : If .δi Δ K} {iff : InfoF If′ If} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If′ Δ K) → ConI If Γ J (V ▷ liftM2 (μ D) g j) → ConI If Γ J V
δ+ {if = if} {iff = iff} j g R D = δ {if = if} {iff = iff} j g R id D

δ- : {if : If .δi Δ K} {iff : InfoF If′ If} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If′ Δ K) → ConI If Γ J V → ConI If Γ J V
δ- {if = if} {iff = iff} j g R D = δ {if = if} {iff = iff} j g R proj₁ D

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


fold : ∀ {D : DescI If Γ J} {X} → ⟦ D ⟧ X ⇶ X → μ D ⇶ X
mapDesc : ∀ {D' : DescI If Γ J} (D : DescI If Γ J) {X} → ∀ p j → ⟦ D' ⟧ X ⇶ X → ⟦ D ⟧ (μ D') p j → ⟦ D ⟧ X p j
mapCon : ∀ {D' : DescI If Γ J} {X V} (C : ConI If Γ J V) → ∀ p j v → ⟦ D' ⟧ X ⇶ X  → ⟦ C ⟧ (μ D') (p , v) j → ⟦ C ⟧ X (p , v) j


fold f p i (con x) = f p i (mapDesc _ p i f x)

mapDesc (C ∷ D) p j f (inj₁ x) = inj₁ (mapCon C p j tt f x)
mapDesc (C ∷ D) p j f (inj₂ y) = inj₂ (mapDesc D p j f y)

mapCon (𝟙 k) p j v f x = x
mapCon (ρ k g C) p j v f (r , x) = fold f (g p) (k (p , v)) r , mapCon C p j v f x
mapCon (σ S h C) p j v f (s , x) = s , mapCon C p j (h (v , s)) f x
mapCon (δ k g R h C) p j v f (r , x) = r , mapCon C p j (h (v , r)) f x

mapμ : ∀ {D : DescI If Γ J} {E : DescI If′ Γ J} → (∀ {X} → ⟦ D ⟧ X ⇶ ⟦ E ⟧ X) → μ D ⇶ μ E
mapμ f p j x = fold (λ p j → con ∘ f p j) p j x


{-
plainDesc : DescI If Γ J → Desc Γ J
plainCon : ConI If Γ J V → Con Γ J V
unplainμ : {D : DescI If Γ J} → μ (plainDesc D) ⇶ μ D
unplainDesc : (D : DescI If Γ J) → (∀ {X} → ⟦ plainDesc D ⟧ X ⇶ ⟦ D ⟧ X)
unplainCon : (D : ConI If Γ J V) → (∀ {X} → ⟦ plainCon D ⟧ X ⇶ ⟦ D ⟧ X)

plainCon (𝟙 j) = 𝟙 j
plainCon (ρ j g D) = ρ j g (plainCon D)
plainCon (σ S h D) = σ S h (plainCon D)
plainCon (δ j g R h D) = δ j g (plainDesc R) (λ { (p , m) → h (p , (unplainμ _ _ m)) }) (plainCon D)

plainDesc []      = []
plainDesc (C ∷ D) = plainCon C ∷ plainDesc D

unplainμ p j x = mapμ (unplainDesc _) p j x

unplainDesc (C ∷ D) p j (inj₁ x) = inj₁ (unplainCon C (p , tt) j x)
unplainDesc (C ∷ D) p j (inj₂ y) = inj₂ (unplainDesc D p j y)

unplainCon (𝟙 j₁) p j x = x
unplainCon (ρ j₁ g D) p j (x , y) = x , unplainCon D _ j y
unplainCon (σ S h D) p j (x , y) = x , unplainCon D _ j y
unplainCon (δ j₁ g R h D) p j (x , y) = unplainμ (g p) (j₁ p) x , unplainCon D _ j y
-}

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
