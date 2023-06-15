\begin{code}
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


infixr 5 _∷_
infixr 10 _▷_

\end{code}

%<*shorthands>
\begin{code}
_⇉_ : (X Y : A → Type) → Type
X ⇉ Y = ∀ a → X a → Y a

_⇶_ : (X Y : A → B → Type) → Type
X ⇶ Y = ∀ a b → X a b → Y a b

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)

! : {A : Type} → A → ⊤
! _ = tt
\end{code}
%</shorthands>

* Telescopes
%<*telescopes>
\begin{code}
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
\end{code}
%</telescopes>
Γ ⊢ A reads as "a value of A in the context of Γ"
ExTel Γ reads as "extension of Γ", and represents a sequence of dependent types which can act as if they were right after the last element of Γ

\begin{code}
private variable
    Γ Δ Θ : Tel P
    U V W : ExTel Γ

_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p
\end{code}
V ⊧ S reads as "an interpretation of S"

%<*tele-shorthands>
\begin{code}
_▷′_ : (Γ : Tel P) (S : Type) → Tel P
Γ ▷′ S = Γ ▷ const S

_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Vxf : (Γ : Tel ⊤) (V W : ExTel Γ) → Type
Vxf Γ V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel p

VxfO : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
VxfO f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)
\end{code}
%</tele-shorthands>
_&_⊢_ is the same as _⊢_, but shortens {V : ExTel Γ} → V ⊢ A to Γ & V ⊢ A
A Cxf is a parameter transformation
A Vxf is a variable transformation
A VxfO is a variable transformation over a parameter transformation

* Combinators
\begin{code}
over : {f : Cxf Γ Δ} → VxfO f V W → ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel
over g (p , v) = _ , g v

VxfO-▷ : ∀ {c : Cxf Γ Δ} (f : VxfO c V W) (S : W ⊢ Type) → VxfO c (V ▷ (S ∘ over f)) (W ▷ S)
VxfO-▷ f S (p , v) = f p , v

VxfO-▷-map : {c : Cxf Γ Δ} (f : VxfO c V W) (S : W ⊢ Type) (T : V ⊢ Type) → (∀ p v → T (p , v) → S (c p , f v)) → VxfO c (V ▷ T) (W ▷ S)
VxfO-▷-map f S T m (v , t) = (f v , m _ v t)

&-▷ : ∀ {S} → (p : ⟦ Δ & W ⟧tel) → S p → ⟦ Δ & W ▷ S ⟧tel
&-▷ (p , v) s = p , v , s

⊧-▷ : ∀ {V : ExTel Γ} {S} → V ⊧ S → Vxf Γ V (V ▷ S)
⊧-▷ s v = v , s (_ , v)
\end{code}

{- -- parameter-variable transformation
Exf : (Γ Δ : Tel ⊤) (V : ExTel Γ) (W : ExTel Δ) → Type
Exf Γ Δ V W = ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel -}

{- Cxf-Exf : Cxf Γ Δ → Exf Γ Δ ∅ ∅
Cxf-Exf f (p , _) = f p , _ 

Vxf-Exf : Vxf Γ V W → Exf Γ Γ V W
Vxf-Exf f (p , v) = p , f v 

Vxf-▷ : (f : Vxf Γ V W) (S : W ⊢ Type) → Vxf Γ (V ▷ (S ∘ Vxf-Exf f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v -}

{- &-drop-▷ : ∀ {S} → ⟦ Γ & V ▷ S ⟧tel → ⟦ Γ & V ⟧tel
&-drop-▷ (p , v , s) = p , v -}

{- Exf-▷ : (f : Exf Γ Δ V W) (S : W ⊢ Type) → Exf Γ Δ (V ▷ (S ∘ f)) (W ▷ S)
Exf-▷ f S (p , v , s) = let (p' , v') = f (p , v) in p' , v' , s -}

* Descriptions
Information bundles (see ConI), a bundle If effectively requests an extra piece of information of, e.g., type 𝟙i when defining a constructor using 𝟙

%<*Info>
\begin{code}
record Info : Type where
  field
    𝟙i : Type
    ρi : Type
    σi : (S : Γ & V ⊢ Type) → Type
    δi : Tel ⊤ → Type → Type
\end{code}
%</Info>
Informed descriptions know who they are! we don't need to introduce ourselves twice, unlike newcomers like (S : Γ & V ⊢ Type)

\begin{code}
open Info public
\end{code}

Information transformers, if there is a transformation InfoF If′ If from the more specific bundle If′ to the less specific bundle If, then a DescI If′ can act as a DescI If
%<*InfoF>
\begin{code}
record InfoF (L R : Info) : Type where
  field
    𝟙f : L .𝟙i → R .𝟙i
    ρf : L .ρi → R .ρi
    σf : {V : ExTel Γ} (S : V ⊢ Type) → L .σi S → R .σi S
    δf : ∀ Γ A → L .δi Γ A → R .δi Γ A
\end{code}
%</InfoF>

\begin{code}
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
\end{code}

%<*Plain>
\begin{code}
Plain : Info
Plain .𝟙i = ⊤
Plain .ρi = ⊤
Plain .σi _ = ⊤
Plain .δi _ _ = ⊤
\end{code}
%</Plain>

No extra information at all! The magic of eta-expansion makes sure that a DescI Plain never gets into someone's way
\begin{code}
private variable
  If If′ : Info
\end{code}


A DescI If Γ J describes a PIType Γ J, augmented by the bundle If, note that an If has no effect the fixpoint!
\begin{code}
data DescI (If : Info) (Γ : Tel ⊤) (J : Type) : Type
data μ (D : DescI If Γ J) (p : ⟦ Γ ⟧tel tt) : J → Type
\end{code}

%<*Con>
\begin{code}
data ConI (If : Info) (Γ : Tel ⊤) (J : Type) (V : ExTel Γ) : Type where
\end{code}
%</Con>
%<*Con-1>
\begin{code}
  𝟙 : {if : If .𝟙i} (j : Γ & V ⊢ J) → ConI If Γ J V
\end{code}
%</Con-1>
%<*Con-rho>
\begin{code}
  ρ  :  {if : If .ρi}
        (j : Γ & V ⊢ J) (g : Γ & V ⊢ ⟦ Γ ⟧tel tt) (C : ConI If Γ J V)
     →  ConI If Γ J V
\end{code}
%</Con-rho>
%<*Con-sigma>
\begin{code}
  σ  :  (S : V ⊢ Type) {if : If .σi S}
        (C : ConI If Γ J (V ▷ S))
     →  ConI If Γ J V
\end{code}
%</Con-sigma>
%<*Con-delta>
\begin{code}
  δ  :  {if : If .δi Δ K} {iff : InfoF If′ If}
        (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (R : DescI If′ Δ K)
        (C : ConI If Γ J (V ▷ liftM2 (μ R) g j))
     →  ConI If Γ J V
\end{code}
%</Con-delta>
%<*Con-v>
\begin{code}
  𝕧  :  (h : Vxf Γ V W) (C : ConI If Γ J W)
     →  ConI If Γ J V
\end{code}
%</Con-v>


𝟙 : ... → X p (j (p , v)) 
ρ : ... → X (g p) (j (p , v)) → ...
σ : ... → (s : S (p , v)) → let w = h (v , s) in ...
δ : ... → (r : μ R (g (p , v)) (j (p , v))) → let w = h (v , r) in ...
-- Maybe g could be Γ & V ⊢ ⟦ Γ ⟧tel tt

The variable transformation 𝕧 lets us choose which variables we retain for the remainder of the description
using them, we can define a - variant which drops the last variable
%<*sigma-pm>
\begin{code}
σ- : (S : Γ & V ⊢ Type) → {if : If .σi S} → ConI If Γ J V → ConI If Γ J V
σ- S {if = if} C = σ S {if = if} (𝕧 proj₁ C)
\end{code}
%</sigma-pm>

\begin{code}
δ- : {if : If .δi Δ K} {iff : InfoF If′ If} → (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : DescI If′ Δ K) → ConI If Γ J V → ConI If Γ J V
δ- {if = if} {iff = iff} j g R D = δ {if = if} {iff = iff} j g R (𝕧 proj₁ D)

-- ordinary recursive field
ρ0 : {if : If .ρi} {V : ExTel Γ} → V ⊢ J → ConI If Γ J V → ConI If Γ J V
ρ0 {if = if} r D = ρ {if = if} r proj₁ D
\end{code}



%<*DescI>
\begin{code}
data DescI If Γ J where
  []   : DescI If Γ J
  _∷_  : ConI If Γ J ∅ → DescI If Γ J → DescI If Γ J
\end{code}
%</DescI>
\end{code}

\begin{code}
Con  = ConI Plain
Desc = DescI Plain

data Tag Γ : Type where
  CT : ExTel Γ → Tag Γ
  DT : Tag Γ

-- PIType Γ J reads as "type with parameters Γ and index J", the universe of types we will take the fixpoint over
\end{code}

%<*PIType>
\begin{code}
PIType : Tel ⊤ → Type → Type
PIType Γ J = ⟦ Γ ⟧tel tt → J → Type
\end{code}
%</PIType>

\begin{code}
module _ {If : Info} where
  UnTag : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnTag Γ J (CT V) = ConI If Γ J V
  UnTag Γ J DT     = DescI If Γ J

  UnFun : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
  UnFun Γ J (CT V) = ⟦ Γ & V ⟧tel → J → Type
  UnFun Γ J DT     = PIType Γ J
\end{code}

* Interpretation
%<*interpretation>
\begin{code}
  ⟦_⟧D : DescI If Γ J → PIType Γ J → PIType Γ J
  ⟦_⟧C : ConI If Γ J V → PIType Γ J → ⟦ Γ & V ⟧tel → J → Type
  ⟦_⟧C (𝟙 j)          X pv i
      = i ≡ j pv
      
  ⟦_⟧C (ρ j f D)      X pv i
      = X (f pv) (j pv) × ⟦ D ⟧C X pv i
      
  ⟦_⟧C (σ S D)        X pv@(p , v) i
      = Σ[ s ∈ S pv ] ⟦ D ⟧C X (p , v , s) i
      
  ⟦_⟧C (δ j g R D)    X pv@(p , v) i
      = Σ[ s ∈ μ R (g pv) (j pv) ] ⟦ D ⟧C X (p , v , s) i
      
  ⟦_⟧C (𝕧 h C)        X pv@(p , v) i
      = ⟦ C ⟧C X (p , h v) i
      
  ⟦_⟧D []             X p i
      = ⊥
      
  ⟦_⟧D (C ∷ D)        X p i
      = (⟦ C ⟧C X (p , tt) i) ⊎ (⟦ D ⟧D X p i)
\end{code}
%</interpretation>

%<*fixpoint>
\begin{code}
data μ D p where
  con : ∀ {i} → ⟦ D ⟧D (μ D) p i → μ D p i
\end{code}
%</fixpoint>

%<*fold-type>
\begin{code}
fold : ∀ {D : DescI If Γ J} {X}
     → ⟦ D ⟧D X ⇶ X → μ D ⇶ X
\end{code}
%</fold-type>

\begin{code}     
mapDesc : ∀ {D' : DescI If Γ J} (D : DescI If Γ J) {X}
        → ∀ p j  → ⟦ D' ⟧D X ⇶ X → ⟦ D ⟧D (μ D') p j → ⟦ D ⟧D X p j
        
mapCon : ∀ {D' : DescI If Γ J} {V} (C : ConI If Γ J V) {X}
       → ∀ p j v → ⟦ D' ⟧D X ⇶ X → ⟦ C ⟧C (μ D') (p , v) j → ⟦ C ⟧C X (p , v) j

fold {D = D} f p i (con x) = f p i (mapDesc D p i f x)

mapDesc (C ∷ D) p j f (inj₁ x) = inj₁ (mapCon C p j tt f x)
mapDesc (C ∷ D) p j f (inj₂ y) = inj₂ (mapDesc D p j f y)

mapCon (𝟙 k)         p j v f      x  = x
mapCon (ρ k g C)     p j v f (r , x) = fold f (g (p , v)) (k (p , v)) r , mapCon C p j v f x
mapCon (σ S C)     p j v f (s , x) = s , mapCon C p j (v , s) f x
mapCon (δ k g R C) p j v f (r , x) = r , mapCon C p j (v , r) f x
mapCon (𝕧 h C) p j v f x = mapCon C p j (h v) f x
\end{code}

%<*par-shorthand>
\begin{code}
par : Γ ⊢ A → Γ & V ⊢ A 
par f = f ∘ (tt ,_) ∘ proj₁

top : ∀ {S} → (Γ ▷ S) ⊧ (S ∘ map₂ proj₁)
top = proj₂ ∘ proj₂

pop : ∀ {S} → Γ ⊢ A → (Γ ▷ S) ⊢ A
pop f (t , p , s) = f (t , p)
\end{code}
%</par-shorthand>

* Examples
\begin{code}
module Descriptions where
\end{code}

%<*NatD>
\begin{code}
  NatD  : Desc ∅ ⊤
  NatD  = 𝟙 _
        ∷ ρ0 _ (𝟙 _)
        ∷ []
\end{code}
%</NatD>


%<*ListTel>
\begin{code}
  ListTel  : Tel ⊤
  ListTel  = ∅ ▷ const Type
\end{code}
%</ListTel>

%<*ListD>
\begin{code}
  ListD : Desc ListTel ⊤
  ListD = 𝟙 _
       ∷ σ- (par top) (ρ0 _ (𝟙 _))
       ∷ []
\end{code}
%</ListD>

%<*VecD>
\begin{code}
  VecD  : Desc ListTel ℕ
  VecD  = 𝟙 (const 0)
        ∷ σ- (par top) (σ (const ℕ) (ρ0 top (𝟙 (suc ∘ top))))
        ∷ []
\end{code}
%</VecD>

{-
  Vec = μ VecD

  module Test where
    open import Data.List

    toList : Vec ⇶ λ A _ → List (proj₂ A)
    toList = fold go
      where
      go : ⟦ VecD ⟧ (λ z _ → List (proj₂ z)) ⇶ (λ z _ → List (proj₂ z))
      go A i (inj₁ _)                       = []
      go A i (inj₂ (inj₁ (x , _ , xs , _))) = x ∷ xs

    vec-1 : Vec (tt , ⊤) 1
    vec-1 = con (inj₂ (inj₁ (tt , 0 , ((con (inj₁ refl)) , refl))))

    list-1 : List ⊤
    list-1 = toList _ _ vec-1
-}

%<*DigitD>
\begin{code}
  DigitD  : Desc (∅ ▷ const Type) ⊤
  DigitD  = σ- (par top) (𝟙 _)
          ∷ σ- (par top) (σ- (par top) (𝟙 _))
          ∷ σ- (par top) (σ- (par top) (σ- (par top) (𝟙 _)))
          ∷ []
\end{code}
%</DigitD>

%<*Node>
\begin{code}
  data Node (A : Type) : Type where
    two    : A → A      → Node A
    three  : A → A → A  → Node A
\end{code}
%</Node>

%<*FingerD>
\begin{code}
  FingerD : Desc (∅ ▷ const Type) ⊤
  FingerD  =  𝟙 _
           ∷  σ- (par top) (𝟙 _)
           ∷  δ- _ (par ((tt ,_) ∘ top)) DigitD
           (  ρ _ (λ { ((_ , A) , _) → (_ , Node A) })
           (  δ- _ (par ((tt ,_) ∘ top)) DigitD (𝟙 _)))
           ∷  []
\end{code}
%</FingerD>
