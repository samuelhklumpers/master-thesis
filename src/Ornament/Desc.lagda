\begin{code}
{-# OPTIONS --type-in-type --with-K #-}

module Ornament.Desc where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum
open import Data.Nat
open import Data.String

open import Function.Base

private variable
  I J K : Type
  A B C X Y Z : Type
  P P′ : Type

infixr 5 _∷_
infixr 10 _▷_
infixr 0 _→₃_
\end{code}

%<*shorthands>
\begin{code}
_⇉_ : (X Y : A → Type) → Type
X ⇉ Y = ∀ a → X a → Y a

_→₃_ : (X Y : A → B → Type) → Type
X →₃ Y = ∀ a b → X a b → Y a b

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)

! : {A : Type} → A → ⊤
! _ = tt
\end{code}
%</shorthands>

\begin{code}
_∘₃_ : ∀ {X Y Z : A → B → Type} → X →₃ Y → (∀ {a b} → Z a b → X a b) → Z →₃ Y
(g ∘₃ f) a b x = g a b (f x)
\end{code}

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
Γ ▷′ S = Γ ▷ λ _ → S

_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Vxf : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
Vxf f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)
\end{code}
%</tele-shorthands>
_&_⊢_ is the same as _⊢_, but shortens {V : ExTel Γ} → V ⊢ A to Γ & V ⊢ A
A Cxf is a parameter transformation
A Vxf is a variable transformation
A Vxf is a variable transformation over a parameter transformation

* Combinators
\begin{code}
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
\end{code}

* Descriptions
Information bundles (see ConI), a bundle If effectively requests an extra piece of information of, e.g., type 𝟙i when defining a constructor using 𝟙

%<*Meta>
\AgdaTarget{Meta, 𝟙i, ρi, σi, δi}
\begin{code}
record Meta : Type where
  field
    𝟙i : Type
    ρi : Type
    σi : (S : Γ & V ⊢ Type) → Type
    δi : Tel ⊤ → Type → Type
\end{code}
%</Meta>
Informed descriptions know who they are! we don't need to introduce ourselves twice, unlike newcomers like (S : Γ & V ⊢ Type)

\begin{code}
open Meta public
\end{code}

Information transformers, if there is a transformation MetaF Me′ If from the more specific bundle Me′ to the less specific bundle If, then a DescI Me′ can act as a DescI Me
%<*MetaF>
\AgdaTarget{MetaF, 𝟙f, ρf, σf, δf}
\begin{code}
record MetaF (L R : Meta) : Type where
  field
    𝟙f : L .𝟙i → R .𝟙i
    ρf : L .ρi → R .ρi
    σf : {V : ExTel Γ} (S : V ⊢ Type) → L .σi S → R .σi S
    δf : ∀ Γ A → L .δi Γ A → R .δi Γ A
\end{code}
%</MetaF>

\begin{code}
open MetaF public

id-MetaF : ∀ {X} → MetaF X X
id-MetaF .𝟙f = id
id-MetaF .ρf = id
id-MetaF .σf _ = id
id-MetaF .δf _ _ = id

_∘MetaF_ : ∀ {X Y Z} → MetaF Y Z → MetaF X Y → MetaF X Z
(ϕ ∘MetaF ψ) .𝟙f x = ϕ .𝟙f (ψ .𝟙f x)
(ϕ ∘MetaF ψ) .ρf x = ϕ .ρf (ψ .ρf x)
(ϕ ∘MetaF ψ) .σf S x = ϕ .σf S (ψ .σf S x)
(ϕ ∘MetaF ψ) .δf Γ A x = ϕ .δf Γ A (ψ .δf Γ A x)
\end{code}

%<*Plain>
\AgdaTarget{Plain}
\begin{code}
Plain : Meta
Plain .𝟙i = ⊤
Plain .ρi = ⊤
Plain .σi _ = ⊤
Plain .δi _ _ = ⊤
\end{code}
%</Plain>


%<*Names>
\AgdaTarget{Names}
\begin{code}
Names : Meta
Names .𝟙i = ⊤
Names .ρi = String
Names .σi _ = String
Names .δi _ _ = String
\end{code}
%</Names>

%<*Countable>
Countable : Meta
Countable .𝟙i = ⊤
Countable .ρi = ⊤
Countable .σi S = ∀ pv → ℕ ↠ S pv
Countable .δi _ _ = ⊤
%</Countable>

No extra information at all! The magic of eta-expansion makes sure that a DescI Plain never gets into someone's way
\begin{code}
private variable
  Me Me′ : Meta
\end{code}


A DescI Me Γ I describes a PIType Γ I, augmented by the bundle Me, note that an Me has no effect the fixpoint!
\begin{code}
mutual
\end{code}

%<*Desc>
\AgdaTarget{DescI}
\begin{code}
  data DescI (Me : Meta) (Γ : Tel ⊤) (I : Type) : Type where
    []   : DescI Me Γ I
    _∷_  : ConI Me Γ ∅ I → DescI Me Γ I → DescI Me Γ I
\end{code} 
%</Desc>

%<*Con>
\AgdaTarget{ConI}
\begin{code}
  data ConI (Me : Meta) (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type where
    𝟙  : {me : Me .𝟙i} (i : Γ & V ⊢ I) → ConI Me Γ V I

    ρ  :  {me : Me .ρi}
          (g : Cxf Γ Γ) (i : Γ & V ⊢ I) (C : ConI Me Γ V I)
       →  ConI Me Γ V I

    σ  :  (S : V ⊢ Type) {me : Me .σi S}
          (w : Vxf id (V ▷ S) W) (C : ConI Me Γ W I)
       →  ConI Me Γ V I

    δ  :  {me : Me .δi Δ J} {iff : MetaF Me′ Me}
          (d : Γ & V ⊢ ⟦ Δ ⟧tel tt) (j : Γ & V ⊢ J) 
          (R : DescI Me′ Δ J) (C : ConI Me Γ V I)
       →  ConI Me Γ V I
\end{code}
%</Con>
𝟙 : ... → X p (i (p , v)) 
ρ : ... → X (g p) (i (p , v)) → ...
σ : ... → (s : S (p , v)) → let w = w (v , s) in ...
δ : ... → (r : μ R (g (p , v)) (i (p , v))) → let w = w (v , r) in ...
-- Maybe g could be Γ & V ⊢ ⟦ Γ ⟧tel tt


* Interpretation
\begin{code}
  infix 10 ⟦_⟧C ⟦_⟧D
\end{code}

%<*interpretation>
\AgdaTarget{⟦\_⟧C, ⟦\_⟧D, ⟧C, ⟧D}
\begin{code}
  ⟦_⟧C : ConI Me Γ V I  → ( ⟦ Γ ⟧tel tt   → I → Type)
                        →   ⟦ Γ & V ⟧tel  → I → Type
  ⟦ 𝟙 i′         ⟧C X pv          i = i ≡ i′ pv
  ⟦ ρ g i′ D     ⟧C X pv@(p , v)  i = X (g p) (i′ pv) × ⟦ D ⟧C X pv i
  ⟦ σ S w D      ⟧C X pv@(p , v)  i = Σ[ s ∈ S pv ] ⟦ D ⟧C X (p , w (v , s)) i
  ⟦ δ d j R D    ⟧C X pv          i = Σ[ s ∈ μ R (d pv) (j pv) ] ⟦ D ⟧C X pv i

  ⟦_⟧D : DescI Me Γ I  → ( ⟦ Γ ⟧tel tt   → I → Type)
                       →   ⟦ Γ ⟧tel tt   → I → Type
  ⟦ []     ⟧D X p i = ⊥
  ⟦ C ∷ D  ⟧D X p i = (⟦ C ⟧C X (p , tt) i) ⊎ (⟦ D ⟧D X p i)
\end{code}
%</interpretation>

%<*fpoint>
\AgdaTarget{μ, con}
\begin{code}
  data μ (D : DescI Me Γ I) (p : ⟦ Γ ⟧tel tt) : I → Type  where
    con : ∀ {i} → ⟦ D ⟧D (μ D) p i → μ D p i
\end{code}
%</fpoint>


The variable transformations (Vxf) in σ and δ let us choose which variables we retain for the remainder of the description
using them, we define "smart" σ and δ, where the + variant retains the last variable, while the - variant drops it
%<*sigma-pm>
\begin{code}
σ+ : (S : Γ & V ⊢ Type) → {me : Me .σi S} → ConI Me Γ (V ▷ S) I → ConI Me Γ V I
σ+ S {me} C = σ S {me = me} id C

σ- : (S : Γ & V ⊢ Type) → {me : Me .σi S} → ConI Me Γ V I → ConI Me Γ V I
σ- S {me} C = σ S {me = me} fst C
\end{code}
%</sigma-pm>

%<*rho-zero>
\begin{code}
ρ0 : {me : Me .ρi} {V : ExTel Γ} → V ⊢ I → ConI Me Γ V I → ConI Me Γ V I
ρ0 {me = me} i D = ρ {me = me} id i D
\end{code}
%</rho-zero>

%<*Plain-synonyms>
\AgdaTarget{Con, Desc}
\begin{code}
Con  = ConI Plain
Desc = DescI Plain
\end{code}
%</Plain-synonyms>

%<*fold-type>
\begin{code}
fold : ∀ {D : DescI Me Γ I} {X} → ⟦ D ⟧D X →₃ X → μ D →₃ X
\end{code}
%</fold-type>

%<*mapFold>
\AgdaTarget{mapDesc, mapCon}
\begin{code}     
mapDesc  : ∀ {D' : DescI Me Γ I} (D : DescI Me Γ I) {X}
         → ∀ p i  → ⟦ D' ⟧D X →₃ X
         → ⟦ D ⟧D (μ D') p i → ⟦ D ⟧D X p i
        
mapCon  : ∀ {D' : DescI Me Γ I} {V} (C : ConI Me Γ V I) {X}
        → ∀ p i v → ⟦ D' ⟧D X →₃ X
        → ⟦ C ⟧C (μ D') (p , v) i → ⟦ C ⟧C X (p , v) i

fold f p i (con x) = f p i (mapDesc _ p i f x)

mapDesc (C ∷ D) p i f (inj₁ x) = inj₁ (mapCon C p i tt f x)
mapDesc (C ∷ D) p i f (inj₂ y) = inj₂ (mapDesc D p i f y)

mapCon (𝟙 j)        p i v f      x   = x
mapCon (ρ g j C)    p i v f (r , x)  = fold f (g p) (j (p , v)) r
                                     , mapCon C p i v f x
mapCon (σ S w C)    p i v f (s , x)  = s , mapCon C p i (w (v , s)) f x
mapCon (δ d j R C)  p i v f (r , x)  = r , mapCon C p i v f x
\end{code}
%</mapFold>

* Examples
\begin{code}
module _ where
\end{code}

%<*NatD-and-ListD>
\begin{code}
  NatD  : Desc ∅ ⊤
  NatD  = zeroD ∷ sucD ∷ []
    where
    zeroD  = 𝟙  _   -- : ℕ
    sucD   = ρ0 _   -- : ℕ
           ( 𝟙  _)  -- → ℕ

  ListD : Desc (∅ ▷ λ _ → Type) ⊤
  ListD = nilD ∷ consD ∷ []
    where
    nilD    = 𝟙 _                       -- : List A
    consD   = σ- (λ ((_ , A) , _) → A)  -- : A
            ( ρ0 _                      -- → List A
            ( 𝟙  _))                    -- → List A
\end{code}
%</NatD-and-ListD>

%<*VecD>
\begin{code}
  VecD  : Desc (∅ ▷ λ _ → Type) ℕ
  VecD = nilD ∷ consD ∷ []
    where
    nilD   = 𝟙 (λ _ → 0)                       -- : Vec A zero
    consD  = σ-  (λ ((_ , A) , _) → A)         -- : A
           ( σ+  (λ _ → ℕ)                     -- → (n : ℕ)
           ( ρ0  (λ (_ , (_ , n)) → n)         -- → Vec A n
           ( 𝟙   (λ (_ , (_ , n)) → suc n))))  -- → Vec A (suc n)
\end{code}
%</VecD>

%<*Pair>
\begin{code}
  Pair : Type → Type
  Pair A = A × A
\end{code}
%</Pair>

%<*RandomD>
\begin{code}
  RandomD  : Desc (∅ ▷ λ _ → Type) ⊤
  RandomD = ZeroD ∷ OneD ∷ TwoD ∷ []
    where
    ZeroD  = 𝟙 _                                  -- : RandomD A
    OneD   = σ-   (λ ((_ , A) , _) → A)           -- : A 
           ( ρ    (λ (_ , A) → (_ , (A × A))) _   -- → Random (A × A)
           ( 𝟙 _))                                -- → Random A
    TwoD   = σ-   (λ ((_ , A) , _) → A)           -- : A
           ( σ-   (λ ((_ , A) , _) → A)           -- → A
           ( ρ    (λ (_ , A) → (_ , (A × A))) _   -- → Random (A × A)
           ( 𝟙 _)))                               -- → Random A
\end{code}
%</RandomD>

%<*DigitD>
\begin{code}
  DigitD  : Desc (∅ ▷ λ _ → Type) ⊤
  DigitD = OneD ∷ TwoD ∷ ThreeD ∷ []
    where
    OneD    =  σ-  (λ ((_ , A) , _) → A)  -- : A
            (  𝟙 _)                       -- → Digit A
    TwoD    =  σ-  (λ ((_ , A) , _) → A)  -- : A 
            (  σ-  (λ ((_ , A) , _) → A)  -- → A 
            (  𝟙 _))                      -- → Digit A
    ThreeD  =  σ-  (λ ((_ , A) , _) → A)  -- : A 
            (  σ-  (λ ((_ , A) , _) → A)  -- → A
            (  σ-  (λ ((_ , A) , _) → A)  -- → A
            (  𝟙 _)))                     -- → Digit A
\end{code}
%</DigitD>

%<*FingerD>
\begin{code}
  FingerD : Desc (∅ ▷ λ _ → Type) ⊤
  FingerD = EmptyD ∷ SingleD ∷ DeepD ∷ []
    where
    EmptyD   =  𝟙 _                                -- : Finger A
    SingleD  =  σ-  (λ ((_ , A) , _) → A)          -- : A
             (  𝟙 _)                               -- → Finger A
    DeepD    =  δ   (λ (p , _) → p) _ DigitD       -- : Digit A 
             (  ρ   (λ (_ , A) → (_ , (A × A))) _  -- → Finger (A × A)
             (  δ   (λ (p , _) → p) _ DigitD       -- → Digit A
             (  𝟙 _)))                             -- → Finger A
\end{code}
%</FingerD>

%<*Number>
\AgdaTarget{Number}
\begin{code}
Number : Meta
Number .𝟙i = ℕ
Number .ρi = ℕ
Number .σi S = ∀ p → S p → ℕ
Number .δi Γ J = (Γ ≡ ∅) × (J ≡ ⊤) × ℕ
\end{code}
%</Number>

%<*toN-type>
\AgdaTarget{value}
\begin{code}
value : {D : DescI Number Γ ⊤} → ∀ {p} → μ D p tt → ℕ
\end{code}
%</toN-type>

\begin{code}
value {D = D} = value-lift D id-MetaF
  where
  value-lift : (D : DescI Me Γ ⊤) → MetaF Me Number → ∀ {p} → μ D p tt → ℕ
  
  value-lift {Me = Me} D ϕ = fold (λ _ _ → value-desc D) _ tt
    where
\end{code}

%<*toN-con>
\AgdaTarget{value-desc, value-con}
\begin{code}
    value-desc : (D : DescI Me Γ ⊤) → ∀ {a b} → ⟦ D ⟧D (λ _ _ → ℕ) a b → ℕ
    value-con : (C : ConI Me Γ V ⊤) → ∀ {a b} → ⟦ C ⟧C (λ _ _ → ℕ) a b → ℕ

    value-desc (C ∷ D) (inj₁ x) = value-con C x
    value-desc (C ∷ D) (inj₂ y) = value-desc D y

    value-con  (𝟙 {me = k} j) refl                          
             = ϕ .𝟙f k

    value-con  (ρ {me = k} g j C)                   (n , x)
             = ϕ .ρf k * n + value-con C x

    value-con  (σ S {me = S→ℕ} h C)                 (s , x)
             = ϕ .σf _ S→ℕ _ s + value-con C x

    value-con  (δ {me = me} {iff = iff} g j R C)    (r , x)
             with ϕ .δf _ _ me
    ...      | refl , refl , k  
             = k * value-lift R (ϕ ∘MetaF iff) r + value-con C x
\end{code}
%</toN-con>

\AgdaTarget{NatND}
\begin{code}
NatND : DescI Number ∅ ⊤
NatND = 𝟙 {me = 0} _
      ∷ ρ0 {me = 1} _ (𝟙 {me = 1} _)
      ∷ []
\end{code}

%<*BinND>
\AgdaTarget{BinND}
\begin{code}
BinND : DescI Number ∅ ⊤
BinND = 0bD ∷ 1bD ∷ 2bD ∷ []
  where
  0bD  = 𝟙 {me = 0} _
  1bD  = ρ0 {me = 2} _
       ( 𝟙 {me = 1} _)
  2bD  = ρ0 {me = 2} _
       ( 𝟙 {me = 2} _)
\end{code}
%</BinND>

%<*PhalanxND>
\AgdaTarget{PhalanxND}
\begin{code}
PhalanxND : DescI Number ∅ ⊤
PhalanxND = 1pD ∷ 2pD ∷ 3pD ∷ []
  where
  1pD  = 𝟙 {me = 1} _
  2pD  = 𝟙 {me = 2} _
  3pD  = 𝟙 {me = 3} _
\end{code}
%</PhalanxND>

%<*CarpalND>
\AgdaTarget{CarpalND}
\begin{code}
CarpalND : DescI Number ∅ ⊤
CarpalND = 0cD ∷ 1cD ∷ 2cD ∷ []
  where
  0cD     = 𝟙 {me = 0} _
  1cD     = 𝟙 {me = 1} _
  2cD     = δ {me = refl , refl , 1} {id-MetaF} _ _ PhalanxND
          ( ρ0 {me = 2} _
          ( δ {me = refl , refl , 1} {id-MetaF} _ _ PhalanxND
          ( 𝟙 {me = 0} _)))
\end{code}
%</CarpalND>
