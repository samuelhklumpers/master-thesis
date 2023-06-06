{-# OPTIONS --type-in-type --with-K #-}


module Ornament.Desc where

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

_⇉_ : (X Y : A → Type) → Type
X ⇉ Y = ∀ a → X a → Y a

_⇶_ : (X Y : A → B → Type) → Type
X ⇶ Y = ∀ a b → X a b → Y a b

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)

! : {A : Type} → A → ⊤
! _ = tt

--* telescopes
data Tel (P : Type) : Type
⟦_⟧tel : (Γ : Tel P) → P → Type

-- Γ ⊢ A reads as "a value of A in the context of Γ"
_⊢_ : (Γ : Tel P) → Type → Type
Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A

-- V ⊧ S reads as "an interpretation of S"
_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p

data Tel P where
  ∅   : Tel P
  _▷_ : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P

⟦ ∅     ⟧tel p = ⊤
⟦ Γ ▷ S ⟧tel p = Σ (⟦ Γ ⟧tel p) (S ∘ (p ,_)) 

-- ExTel Γ reads as "extension of Γ", and represents a sequence of dependent types which can act as if they were right after the last element of Γ
ExTel : Tel ⊤ → Type
ExTel Γ = Tel (⟦ Γ ⟧tel tt)

-- the same as _⊢_, but shortens {V : ExTel Γ} → V ⊢ A to Γ & V ⊢ A
_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

private variable
  Γ Δ Θ : Tel P
  U V W : ExTel Γ

-- parameter transformation
Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

-- parameter-variable transformation
Exf : (Γ Δ : Tel ⊤) (V : ExTel Γ) (W : ExTel Δ) → Type
Exf Γ Δ V W = ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel

-- variable transformation
Vxf : (Γ : Tel ⊤) (V W : ExTel Γ) → Type
Vxf Γ V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel p

-- variable transformation over parameter transformation
VxfO : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
VxfO f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)

-- combinators
over : {f : Cxf Γ Δ} → VxfO f V W → Exf Γ Δ V W
over g (p , v) = _ , g v

Cxf-Exf : Cxf Γ Δ → Exf Γ Δ ∅ ∅
Cxf-Exf f (p , _) = f p , _ 

Vxf-Exf : Vxf Γ V W → Exf Γ Γ V W
Vxf-Exf f (p , v) = p , f v

Vxf-▷ : (f : Vxf Γ V W) (S : W ⊢ Type) → Vxf Γ (V ▷ (S ∘ Vxf-Exf f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v

VxfO-▷ : ∀ {c : Cxf Γ Δ} (f : VxfO c V W) (S : W ⊢ Type) → VxfO c (V ▷ (S ∘ over f)) (W ▷ S)
VxfO-▷ f S (p , v) = f p , v

VxfO-▷-map : {c : Cxf Γ Δ} (f : VxfO c V W) (S : W ⊢ Type) (T : V ⊢ Type) → (∀ p v → T (p , v) → S (c p , f v)) → VxfO c (V ▷ T) (W ▷ S)
VxfO-▷-map f S T m (v , t) = (f v , m _ v t)

Exf-▷ : (f : Exf Γ Δ V W) (S : W ⊢ Type) → Exf Γ Δ (V ▷ (S ∘ f)) (W ▷ S)
Exf-▷ f S (p , v , s) = let (p' , v') = f (p , v) in p' , v' , s

&-▷ : ∀ {S} → (p : ⟦ Δ & W ⟧tel) → S p → ⟦ Δ & W ▷ S ⟧tel
&-▷ (p , v) s = p , v , s

&-drop-▷ : ∀ {S} → ⟦ Γ & V ▷ S ⟧tel → ⟦ Γ & V ⟧tel
&-drop-▷ (p , v , s) = p , v

⊧-▷ : ∀ {V : ExTel Γ} {S} → V ⊧ S → Vxf Γ V (V ▷ S)
⊧-▷ s v = v , s (_ , v)


--* descriptions
-- information bundles (see ConI), a bundle If effectively requests an extra piece of information of, e.g., type 𝟙i when defining a constructor using 𝟙
record Info : Type where
  field
    𝟙i : Type
    ρi : Type
    σi : (S : Γ & V ⊢ Type) → Type
    δi : Tel ⊤ → Type → Type
    -- informed descriptions know who they are! we don't need to introduce ourselves twice, unlike newcomers like (S : Γ & V ⊢ Type)

open Info public

-- information transformers, if there is a transformation InfoF If′ If from the more specific bundle If′ to the less specific bundle If, then a DescI If′ can act as a DescI If
record InfoF (L R : Info) : Type where
  field
    𝟙f : L .𝟙i → R .𝟙i
    ρf : L .ρi → R .ρi
    σf : {V : ExTel Γ} (S : V ⊢ Type) → L .σi S → R .σi S
    δf : ∀ Γ A → L .δi Γ A → R .δi Γ A

open InfoF public

id-InfoF : ∀ {X} → InfoF X X
id-InfoF .𝟙f = id
id-InfoF .ρf = id
id-InfoF .σf _ = id
id-InfoF .δf _ _ = id

_∘InfoF_ : ∀ {X Y Z} → InfoF Y Z → InfoF X Y → InfoF X Z
(ϕ ∘InfoF ψ) .𝟙f x = ϕ .𝟙f (ψ .𝟙f x)
(ϕ ∘InfoF ψ) .ρf x = ϕ .ρf (ψ .ρf x)
(ϕ ∘InfoF ψ) .σf S x = ϕ .σf S (ψ .σf S x)
(ϕ ∘InfoF ψ) .δf Γ A x = ϕ .δf Γ A (ψ .δf Γ A x)

-- no extra information at all! the magic of eta-expansion makes sure that a DescI Plain never gets into someone's way
Plain : Info
Plain .𝟙i = ⊤
Plain .ρi = ⊤
Plain .σi _ = ⊤
Plain .δi _ _ = ⊤

private variable
  If If′ : Info

-- a DescI If Γ J describes a PIType Γ J, augmented by the bundle If, note that If has no effect the fixpoint!
data DescI (If : Info) (Γ : Tel ⊤) (J : Type) : Type
data μ (D : DescI If Γ J) (p : ⟦ Γ ⟧tel tt) : J → Type
data ConI (If : Info) (Γ : Tel ⊤) (J : Type) (V : ExTel Γ) : Type where
  -- ... → X p (j (p , v)) 
  𝟙 : {if : If .𝟙i} (j : Γ & V ⊢ J) → ConI If Γ J V

  -- ... → X (g p) (j (p , v)) → ...
  ρ : {if : If .ρi} (j : Γ & V ⊢ J) (g : Cxf Γ Γ) (C : ConI If Γ J V) → ConI If Γ J V
  -- maybe g could be Γ & V ⊢ ⟦ Γ ⟧tel tt

  -- ... → (s : S (p , v)) → let w = h (v , s) in ...
  σ : (S : V ⊢ Type) {if : If .σi S} (h : Vxf Γ (V ▷ S) W) (C : ConI If Γ J W) → ConI If Γ J V

  -- ... → (r : μ R (g (p , v)) (j (p , v))) → let w = h (v , r) in ...
  δ : {if : If .δi Δ K} {iff : InfoF If′ If}
      (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (R : DescI If′ Δ K) (h : Vxf Γ (V ▷ liftM2 (μ R) g j) W)
      (C : ConI If Γ J W)
    → ConI If Γ J V


-- the variable transformations (Vxf) in σ and δ let us choose which variables we retain for the remainder of the description
-- using them, we define "smart" σ and δ, where the + variant retains the last variable, while the - variant drops it
σ+ : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J (V ▷ S) → ConI If Γ J V
σ+ S {if = if} C = σ S {if = if} id C

σ- : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J V → ConI If Γ J V
σ- S {if = if} C = σ S {if = if} proj₁ C

δ+ : {if : If .δi Δ K} {iff : InfoF If′ If} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If′ Δ K) → ConI If Γ J (V ▷ liftM2 (μ D) g j) → ConI If Γ J V
δ+ {if = if} {iff = iff} j g R D = δ {if = if} {iff = iff} j g R id D

δ- : {if : If .δi Δ K} {iff : InfoF If′ If} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If′ Δ K) → ConI If Γ J V → ConI If Γ J V
δ- {if = if} {iff = iff} j g R D = δ {if = if} {iff = iff} j g R proj₁ D

-- ordinary recursive field
ρ0 : {if : If .ρi} {V : ExTel Γ} → V ⊢ J → ConI If Γ J V → ConI If Γ J V
ρ0 {if = if} r D = ρ {if = if} r id D


data DescI If Γ J where
  []  : DescI If Γ J
  _∷_ : ConI If Γ J ∅ → DescI If Γ J → DescI If Γ J 

Con  = ConI Plain
Desc = DescI Plain

data Tag Γ : Type where
  CT : ExTel Γ → Tag Γ
  DT : Tag Γ

-- PIType Γ J reads as "type with parameters Γ and index J", the universe of types we will take the fixpoint over
PIType : Tel ⊤ → Type → Type
PIType Γ J = ⟦ Γ ⟧tel tt → J → Type

module _ {If : Info} where
  UnTag : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnTag Γ J (CT V) = ConI If Γ J V
  UnTag Γ J DT     = DescI If Γ J

  UnFun : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnFun Γ J (CT V) = ⟦ Γ & V ⟧tel → J → Type
  UnFun Γ J DT     = PIType Γ J

  -- interpretation
  ⟦_⟧ : {t : Tag Γ} → UnTag Γ J t → PIType Γ J → UnFun Γ J t
  ⟦_⟧ {t = CT V} (𝟙 j)         X pv i         = i ≡ j pv
  ⟦_⟧ {t = CT V} (ρ j f D)     X pv@(p , v) i = X (f p) (j pv) × ⟦ D ⟧ X pv i
  ⟦_⟧ {t = CT V} (σ S h D)     X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ D ⟧ X (p , h (v , s)) i
  ⟦_⟧ {t = CT V} (δ j g R h D) X pv@(p , v) i = Σ[ s ∈ μ R (g pv) (j pv) ] ⟦ D ⟧ X (p , h (v , s)) i
  ⟦_⟧ {t = DT}   []            X p i = ⊥
  ⟦_⟧ {t = DT}   (C ∷ D)       X p i = (⟦ C ⟧ X (p , tt) i) ⊎ (⟦ D ⟧ X p i) 


data μ D p where
  con : ∀ {i} → ⟦ D ⟧ (μ D) p i → μ D p i


fold : ∀ {D : DescI If Γ J} {X}
     → ⟦ D ⟧ X ⇶ X → μ D ⇶ X
     
mapDesc : ∀ {D' : DescI If Γ J} (D : DescI If Γ J) {X}
        → ∀ p j  → ⟦ D' ⟧ X ⇶ X → ⟦ D ⟧ (μ D') p j → ⟦ D ⟧ X p j
        
mapCon : ∀ {D' : DescI If Γ J} {V} (C : ConI If Γ J V) {X}
       → ∀ p j v → ⟦ D' ⟧ X ⇶ X → ⟦ C ⟧ (μ D') (p , v) j → ⟦ C ⟧ X (p , v) j

fold f p i (con x) = f p i (mapDesc _ p i f x)

mapDesc (C ∷ D) p j f (inj₁ x) = inj₁ (mapCon C p j tt f x)
mapDesc (C ∷ D) p j f (inj₂ y) = inj₂ (mapDesc D p j f y)

mapCon (𝟙 k)         p j v f      x  = x
mapCon (ρ k g C)     p j v f (r , x) = fold f (g p) (k (p , v)) r , mapCon C p j v f x
mapCon (σ S h C)     p j v f (s , x) = s , mapCon C p j (h (v , s)) f x
mapCon (δ k g R h C) p j v f (r , x) = r , mapCon C p j (h (v , r)) f x

par : Γ ⊢ A → Γ & V ⊢ A 
par f = f ∘ (tt ,_) ∘ proj₁

-- I hope this does what I think it does
top : ∀ {S} → (Γ ▷ S) ⊧ λ { (t , p , _) → S (t , p) }
top = proj₂ ∘ proj₂

pop : ∀ {S} → Γ ⊢ A → (Γ ▷ S) ⊢ A
pop f (t , p , s) = f (t , p)

-- examples
module Descriptions where
  NatD : Desc ∅ ⊤
  NatD = 𝟙 _
       ∷ ρ0 _ (𝟙 _)
       ∷ []

  VecD : Desc (∅ ▷ const Type) ℕ
  VecD = 𝟙 (const 0)
       ∷ σ- (par top) (σ+ (const ℕ) (ρ0 top (𝟙 (suc ∘ top))))
       ∷ []

  Vec = μ VecD

  vec-1 : Vec (tt , ⊤) 1
  vec-1 = con (inj₂ (inj₁ (tt , 0 , ((con (inj₁ refl)) , refl))))

  DigitD : Desc (∅ ▷ const Type) ⊤
  DigitD = σ- (par top) (𝟙 _)
         ∷ σ- (par top) (σ- (par top) (𝟙 _))
         ∷ σ- (par top) (σ- (par top) (σ- (par top) (𝟙 _)))
         ∷ []
         
  data Node (A : Type) : Type where
    two   : A → A     → Node A
    three : A → A → A → Node A

  FingerD : Desc (∅ ▷ const Type) ⊤
  FingerD = 𝟙 _
          ∷ σ- (par top) (𝟙 _)
          ∷ δ- _ (par ((tt ,_) ∘ top)) DigitD (ρ _ (λ { (_ , A) → (_ , Node A) }) (δ- _ (par ((tt ,_) ∘ top)) DigitD (𝟙 _)))
          ∷ []

