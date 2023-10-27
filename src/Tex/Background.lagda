\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )
open import Function.Base

module Tex.Background where

private variable
  A B C : Type
\end{code}

%<*Bool>
\AgdaTarget{Bool}
\AgdaTarget{true, false}
\begin{code}
data Bool : Type where
    false  : Bool
    true   : Bool 
\end{code}
%</Bool>

%<*ternary>
\begin{code}
_🍧_🌶_ : Bool → A → A → A
false 🍧 t 🌶 e = e
true 🍧 t 🌶 e = t
\end{code}
%</ternary>

%<*conditional>
\begin{code}
if_then_else_ : Bool → A → A → A
if false  then t else e = e
if true   then t else e = t
\end{code}
%</conditional>

%<*Nat>
\AgdaTarget{ℕ}
\begin{code}
data ℕ : Type where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</Nat>

\begin{code}
private variable
  n m : ℕ

_+_ : (n m : ℕ) → ℕ
zero  + m = m
suc n + m = suc (n + m)
\end{code}

%<*lt>
\begin{code}
_<?_ : (n m : ℕ) → Bool
n      <? zero   = false
zero   <? suc m  = true
suc n  <? suc m  = n <? m
\end{code}
%</lt>

%<*List>
\AgdaTarget{List}
\begin{code}
data List (A : Type) : Type where
  []   : List A
  _∷_  : A → List A → List A
\end{code}
%</List>

%<*Maybe>
\AgdaTarget{nothing, just}
\AgdaTarget{Maybe}
\begin{code}
data Maybe (A : Type) : Type where
  nothing  : Maybe A
  just     : A → Maybe A
\end{code}
%</Maybe>

%<*lookup-list>
\begin{code}
lookup? : List A → ℕ → Maybe A
lookup? []        n        = nothing
lookup? (x ∷ xs)  zero     = just x
lookup? (x ∷ xs)  (suc n)  = lookup? xs n
\end{code}
%</lookup-list>

%<*length>
\AgdaTarget{length}
\begin{code}
length : List A → ℕ
length []        = zero
length (x ∷ xs)  = suc (length xs)
\end{code}
%</length>

%<*Fin>
\AgdaTarget{Fin}
\begin{code}
data Fin : ℕ → Type where
  zero  :          Fin (suc n)
  suc   : Fin n  → Fin (suc n)
\end{code}
%</Fin>

%<*Vec>
\AgdaTarget{Vec}
\begin{code}
data Vec (A : Type) : ℕ → Type where
  []   :                Vec A zero
  _∷_  : A → Vec A n →  Vec A (suc n)
\end{code}
%</Vec>

%<*toList>
\AgdaTarget{toList}
\begin{code}
toList : Vec A n → List A
toList []        = []
toList (x ∷ xs)  = x ∷ toList xs
\end{code}
%</toList>

%<*toVec>
\AgdaTarget{toVec}
\begin{code}
toVec : (xs : List A) → Vec A (length xs)
toVec []        = []
toVec (x ∷ xs)  = x ∷ toVec xs
\end{code}
%</toVec>

%<*lookup>
\AgdaTarget{lookup}
\begin{code}
lookup : ∀ {n} → Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i
\end{code}
%</lookup>

%<*equiv>
\AgdaTarget{\_≡\_, ≡}
\begin{code}
data _≡_ (a : A) : A → Type where
  refl : a ≡ a
\end{code}
%</equiv>

%<*ltF>
\AgdaTarget{\_<\_, <}
\begin{code}
data _<_ : (n m : ℕ) → Type where
  z<s : zero < suc m
  s<s : n < m → suc n < suc m
\end{code}
%</ltF>

\begin{code}
infix 5 _<_

{-# BUILTIN EQUALITY _≡_ #-}
\end{code}

%<*insert>
\AgdaTarget{insert}
\begin{code}
insert : ∀ {n} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insert xs        zero     y = y ∷ xs
insert (x ∷ xs)  (suc i)  y = x ∷ insert xs i y
\end{code}
%</insert>

%<*lookup-insert-type>
\AgdaTarget{lookup-insert-type}
\begin{code}
lookup-insert-type : ∀ {n} → Vec A n → Fin (suc n) → A → Type
lookup-insert-type xs i x = lookup (insert xs i x) i ≡ x
\end{code}
%</lookup-insert-type>

%<*equiv-lemmas>
\AgdaTarget{trans}
\AgdaTarget{cong}
\AgdaTarget{subst}
\begin{code}
trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

cong : {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

subst : {a b : A} → (P : A → Type) → a ≡ b → P a → P b
subst P refl x = x
\end{code}
%</equiv-lemmas>

%<*lookup-insert>
\AgdaTarget{lookup-insert}
\begin{code}
lookup-insert  : ∀ {n} (xs : Vec A n) (i : Fin (suc n)) (y : A)
               → lookup-insert-type xs i y
lookup-insert []        zero     y = refl
lookup-insert (x ∷ xs)  zero     y = refl
lookup-insert (x ∷ xs)  (suc i)  y = lookup-insert xs i y
\end{code}
%</lookup-insert>

%<*uplus>
\AgdaTarget{\_⊎\_, ⊎}
\AgdaTarget{inj₁}
\AgdaTarget{inj₂}
\begin{code}
data _⊎_ A B : Type where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
\end{code}
%</uplus>

\begin{code}
infixr 5 _,_
infix 10 _⊎_
\end{code}

%<*product>
\AgdaTarget{\_×\_, ×}
\AgdaTarget{\_\,\_, \,}
\AgdaTarget{fst}
\AgdaTarget{snd}
\begin{code}
record _×_ A B : Type where
  constructor _,_
  field
    fst : A
    snd : B
\end{code}
%</product>

\begin{code}
open _×_ public

infixl 5 _×_
\end{code}

%<*true>
\AgdaTarget{⊤}
\AgdaTarget{tt}
\begin{code}
record ⊤ : Type where
  constructor tt
\end{code}
%</true>

%<*false>
\AgdaTarget{⊥}
\begin{code}
data ⊥ : Type where
\end{code}
%</false>

%<*not>
\AgdaTarget{¬\_, ¬}
\begin{code}
¬_ : Type → Type
¬ A = A → ⊥
\end{code}
%</not>

%<*exists>
\AgdaTarget{Σ\_, Σ}
\begin{code}
record Σ A (P : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : P fst
\end{code}
%</exists>

\begin{code}
open Σ

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (P : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

infix 4 Σ-syntax
\end{code}

%<*sigma-syntax>
\begin{code}
syntax Σ-syntax A (λ x → P) = Σ[ x ∈ A ] P
\end{code}
%</sigma-syntax>

%<*forall>
\begin{code}
data ∀′ A (P : A → Type) : Type where
  all : (∀ a → P a) → ∀′ A P
\end{code}
%</forall>

%<*U-fin>
\AgdaTarget{U-fin}
\begin{code}
data U-fin : Type where
  𝟘 𝟙      : U-fin
  _⊕_ _⊗_  : U-fin → U-fin → U-fin
\end{code}
%</U-fin>

%<*int-fin>
\AgdaTarget{⟦\_⟧fin, ⟧fin}
\begin{code}
⟦_⟧fin : U-fin → Type
⟦ 𝟘     ⟧fin = ⊥
⟦ 𝟙     ⟧fin = ⊤
⟦ D ⊕ E ⟧fin = ⟦ D ⟧fin ⊎ ⟦ E ⟧fin
⟦ D ⊗ E ⟧fin = ⟦ D ⟧fin × ⟦ E ⟧fin
\end{code}
%</int-fin>

%<*BoolD>
\begin{code}
BoolD : U-fin
BoolD = 𝟙 ⊕ 𝟙
\end{code}
%</BoolD>

%<*U-rec>
\AgdaTarget{U-rec}
\begin{code}
data U-rec : Type where
  𝟙 ρ      : U-rec
  _⊕_ _⊗_  : U-rec → U-rec → U-rec
\end{code}
%</U-rec>

%<*int-rec>
\AgdaTarget{⟦\_⟧rec, ⟧rec}
\begin{code}
⟦_⟧rec : U-rec → Type → Type
⟦ 𝟙      ⟧rec X = ⊤
⟦ ρ      ⟧rec X = X
⟦ D ⊕ E  ⟧rec X = (⟦ D ⟧rec X) ⊎ (⟦ E ⟧rec X)
⟦ D ⊗ E  ⟧rec X = (⟦ D ⟧rec X) × (⟦ E ⟧rec X)
\end{code}
%</int-rec>

%<*mu-rec>
\AgdaTarget{μ-rec}
\begin{code}
data μ-rec (D : U-rec) : Type where
  con : ⟦ D ⟧rec (μ-rec D) → μ-rec D
\end{code}
%</mu-rec>


\begin{code}
module NatD-bad where
\end{code}

%<*NatD>
\begin{code}
  NatD  : U-rec
  NatD  = 𝟙 ⊕ ρ
\end{code}
%</NatD>

\begin{code}
infixr 5 _∷_
\end{code}

%<*U-sop>
\AgdaTarget{Con-sop}
\AgdaTarget{U-sop}
\begin{code}
data Con-sop : Type
data U-sop : Type where
  []  : U-sop
  _∷_ : Con-sop → U-sop → U-sop
\end{code}
%</U-sop>

%<*Con-sop>
\begin{code}
data Con-sop where
  𝟙    : Con-sop
  ρ    : Con-sop → Con-sop
  σ    : (S : Type) → (S → Con-sop) → Con-sop
\end{code}
%</Con-sop>

%<*int-sop>
\AgdaTarget{⟦\_⟧U-sop, ⟧U-sop}
\AgdaTarget{⟦\_⟧C-sop, ⟧C-sop}
\begin{code}
⟦_⟧U-sop : U-sop → Type → Type
⟦_⟧C-sop : Con-sop → Type → Type

⟦ []    ⟧U-sop X = ⊥
⟦ C ∷ D ⟧U-sop X = ⟦ C ⟧C-sop X × ⟦ D ⟧U-sop X

⟦ 𝟙     ⟧C-sop X = ⊤
⟦ ρ C   ⟧C-sop X = X × ⟦ C ⟧C-sop X
⟦ σ S f ⟧C-sop X = Σ[ s ∈ S ] ⟦ f s ⟧C-sop X
\end{code}
%</int-sop>

\begin{code}
module ListD′ where
\end{code}
%<*ListD-bad>
\begin{code}
  ListD : Type → U-sop
  ListD A = 𝟙
          ∷ (σ A λ _ → ρ 𝟙)
          ∷ []
\end{code}
%</ListD-bad>


\begin{code}
infixl 5 _▷_

private variable
  P : Type
\end{code}

%<*Tel-simple>
\begin{code}
data Tel′ : Type
⟦_⟧tel′ : Tel′ → Type

data Tel′ where
  ∅    : Tel′
  _▷_  : (Γ : Tel′) (S : ⟦ Γ ⟧tel′ → Type) → Tel′
\end{code}
%</Tel-simple>

%<*int-simple>
\begin{code}
⟦ ∅      ⟧tel′ = ⊤
⟦ Γ ▷ S  ⟧tel′ = Σ ⟦ Γ ⟧tel′ S
\end{code}
%</int-simple>

%<*sigma-tel>
\begin{code}
Σ-Tel : Tel′
Σ-Tel = ∅ ▷ const Type ▷ (λ A → A → Type) ∘ snd
\end{code}
%</sigma-tel>

%<*Tel-type>
\AgdaTarget{Tel}
\AgdaTarget{⟦\_⟧tel}
\begin{code}
data Tel (P : Type) : Type
⟦_⟧tel : Tel P → P → Type
\end{code}
%</Tel-type>

%<*entails>
\AgdaTarget{\_⊢\_, ⊢}
\begin{code}
_⊢_ : Tel P → Type → Type
Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A
\end{code}
%</entails>

%<*Tel-def>
\AgdaTarget{∅, \_▷\_, ▷}
\begin{code}
data Tel P where
  ∅    : Tel P
  _▷_  : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P

⟦ ∅      ⟧tel p = ⊤
⟦ Γ ▷ S  ⟧tel p = Σ[ x ∈ ⟦ Γ ⟧tel p ] S (p , x)
\end{code}
%</Tel-def>

%<*ExTel>
\AgdaTarget{ExTel}
\begin{code}
ExTel : Tel ⊤ → Type
ExTel Γ = Tel (⟦ Γ ⟧tel tt)
\end{code}
%</ExTel>

\begin{code}[hide]
private variable
  Γ Δ : Tel ⊤
  V W : ExTel Γ
  I : Type
\end{code}

%<*int-ExTel>
\AgdaTarget{⟦\_\&\_⟧tel}
\begin{code}
⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel
\end{code}
%</int-ExTel>

%<*tele-helpers>
\begin{code}
map-var : ∀ {A B C} → (∀ {a} → B a → C a) → Σ A B → Σ A C
map-var f (a , b) = (a , f b)

Cxf : (Δ Γ : Tel P) → Type
Cxf Δ Γ = ∀ {p} → ⟦ Δ ⟧tel p → ⟦ Γ ⟧tel p

Vxf : Cxf Δ Γ → (W : ExTel Δ) (V : ExTel Γ) → Type
Vxf g W V = ∀ {d} → ⟦ W ⟧tel d → ⟦ V ⟧tel (g d)

var→par : {g : Cxf Δ Γ} → Vxf g W V → ⟦ Δ & W ⟧tel → ⟦ Γ & V ⟧tel
var→par v (d , w) = _ , v w

Vxf-▷ :  {g : Cxf Δ Γ} (v : Vxf g W V) (S : V ⊢ Type)
       →  Vxf g (W ▷ (S ∘ var→par v)) (V ▷ S)
Vxf-▷ v S (p , w) = v p , w
\end{code}
%</tele-helpers>

%<*U-par>
\AgdaTarget{Con-par}
\AgdaTarget{U-par}
\begin{code}
data Con-par (Γ : Tel ⊤) (V : ExTel Γ) : Type
data U-par (Γ : Tel ⊤) : Type where
  []   : U-par Γ
  _∷_  : Con-par Γ ∅ → U-par Γ → U-par Γ

data Con-par Γ V where
  𝟙  : Con-par Γ V
  ρ  : Con-par Γ V → Con-par Γ V
  σ  : (S : V ⊢ Type) → Con-par Γ (V ▷ S) → Con-par Γ V
\end{code}
%</U-par>

%<*int-par>
\AgdaTarget{⟦\_⟧U-par, ⟧U-par}
\AgdaTarget{⟦\_⟧C-par, ⟧C-par}
\begin{code}
⟦_⟧U-par : U-par Γ → (⟦ Γ ⟧tel tt → Type) → ⟦ Γ ⟧tel tt → Type
⟦_⟧C-par : Con-par Γ V → (⟦ Γ & V ⟧tel → Type) → ⟦ Γ & V ⟧tel → Type

⟦ []     ⟧U-par X p  = ⊥
⟦ C ∷ D  ⟧U-par X p  = ⟦ C ⟧C-par (X ∘ fst) (p , tt) × ⟦ D ⟧U-par X p

⟦ 𝟙      ⟧C-par X pv          = ⊤
⟦ ρ C    ⟧C-par X pv          = X pv × ⟦ C ⟧C-par X pv
⟦ σ S C  ⟧C-par X pv@(p , v)
  = Σ[ s ∈ S pv ] ⟦ C ⟧C-par (X ∘ map-var fst) (p , v , s)
\end{code}
%</int-par>

\begin{code}
module ListD-bad where
\end{code}
%<*ListD>
\begin{code}
  ListD : U-par (∅ ▷ const Type)
  ListD  =  𝟙
         ∷  σ (λ { ((_ , A) , _) → A })
         (  ρ
            𝟙)
         ∷  []
\end{code}
%</ListD>

%<*SigmaD>
\begin{code}
SigmaD : U-par (∅ ▷ const Type ▷ λ { (_ , _ , A) → A → Type })
SigmaD  =  σ (λ { (((_ , A) , _) ,  _)       → A } )
        (  σ (λ { ((_       , B) , (_ , a))  → B a } )
           𝟙)
        ∷  []
\end{code}
%</SigmaD>


%<*U-ix>
\AgdaTarget{Con-ix}
\AgdaTarget{U-ix}
\begin{code}
data Con-ix (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-ix (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-ix Γ I
  _∷_  : Con-ix Γ ∅ I → U-ix Γ I → U-ix Γ I
\end{code}
%</U-ix>

%<*Con-ix>
\begin{code}
data Con-ix Γ V I where
  𝟙   : V ⊢ I → Con-ix Γ V I
  ρ   : V ⊢ I → Con-ix Γ V I → Con-ix Γ V I
  σ   : (S : V ⊢ Type) → Con-ix Γ (V ▷ S) I → Con-ix Γ V I
\end{code}
%</Con-ix>

%<*int-ix>
\AgdaTarget{⟦\_⟧C, ⟧C}
\AgdaTarget{⟦\_⟧D, ⟧D}
\begin{code}
⟦_⟧C : Con-ix Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C X pv i = i ≡ (j pv)
⟦ ρ j C  ⟧C X pv@(p , v) i = X p (j pv) × ⟦ C ⟧C X pv i
⟦ σ S C  ⟧C X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C X (p , v , s) i

⟦_⟧D : U-ix Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
⟦ []      ⟧D X p i = ⊥
⟦ C ∷ Cs  ⟧D X p i = ⟦ C ⟧C X (p , tt) i  ⊎ ⟦ Cs ⟧D X p i
\end{code}
%</int-ix>

%<*mu-ix>
\AgdaTarget{μ-ix}
\begin{code}
data μ-ix (D : U-ix Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
  con : ⟦ D ⟧D (μ-ix D) p i → μ-ix D p i
\end{code}
%</mu-ix>

%<*FinD>
\begin{code}
FinD : U-ix ∅ ℕ
FinD = σ (const ℕ)
     ( 𝟙 (λ { (_ , (_ , n)) → suc n } ))
     ∷ σ (const ℕ)
     ( ρ (λ { (_ , (_ , n)) → n } )
     ( 𝟙 (λ { (_ , (_ , n)) → suc n } )))
     ∷ []
\end{code}
%</FinD>

%<*VecD>
\begin{code}
VecD : U-ix (∅ ▷ const Type) ℕ
VecD = 𝟙 (const zero)
     ∷  σ (const ℕ)
     (  σ (λ { ((_ , A) , _) → A } )
     (  ρ (λ { (_ , ((_ , n) , _)) → n } )
     (  𝟙 (λ { (_ , ((_ , n) , _)) → suc n } ))))
     ∷ []
\end{code}
%</VecD>

%<*fold-type>
\begin{code}
_⇶_ : (X Y : A → B → Type) → Type
X ⇶ Y = ∀ a b → X a b → Y a b

fold : ∀ {D : U-ix Γ I} {X}
     → ⟦ D ⟧D X ⇶ X → μ-ix D ⇶ X
\end{code}
%</fold-type>

%<*fold>
\begin{code}     
mapDesc : ∀ {I} {D' : U-ix Γ I} (D : U-ix Γ I) {X}
        → ∀ p j  → ⟦ D' ⟧D X ⇶ X → ⟦ D ⟧D (μ-ix D') p j → ⟦ D ⟧D X p j
        
mapCon : ∀ {I} {D' : U-ix Γ I} {V} (C : Con-ix Γ V I) {X}
       → ∀ p j v → ⟦ D' ⟧D X ⇶ X → ⟦ C ⟧C (μ-ix D') (p , v) j → ⟦ C ⟧C X (p , v) j

fold f p i (con x) = f p i (mapDesc _ p i f x)

mapDesc (CD ∷ D) p j f (inj₁ x) = inj₁ (mapCon CD p j tt f x)
mapDesc (CD ∷ D) p j f (inj₂ y) = inj₂ (mapDesc D p j f y)

mapCon (𝟙 i)     p j v f       x  = x
mapCon (ρ i CD)  p j v f (r ,  x) = fold f p (i (p , v)) r , mapCon CD p j v f x
mapCon (σ S CD)  p j v f (s ,  x) = s , mapCon CD p j (v , s) f x
\end{code}
%</fold>

\begin{code}
private variable
  J : Type
  D E : U-ix Γ I
\end{code}

%<*new-Nat-List>
\begin{code}
! : A → ⊤
! x = tt

NatD  : U-ix ∅ ⊤
NatD  = 𝟙 !
      ∷ ρ !
      ( 𝟙 !)
      ∷ []

ListD  : U-ix (∅ ▷ const Type) ⊤
ListD  = 𝟙 !
       ∷ σ (λ { ((_ , A) , _) → A })
       ( ρ !
       ( 𝟙 ! ))
       ∷ []
\end{code}
%</new-Nat-List>


\begin{code}
postulate
\end{code}


%<*foldr-type>
\begin{code}
  foldr  : {X : Type → Type}
         → (∀ A → ⊤ ⊎ (A × X A) → X A)
         → ∀ B → List B → X B
\end{code}
%</foldr-type>

%<*usual-fold>
\begin{code}
  foldr′ : ∀ A B → (⊤ ⊎ (A × B) → B) → List A → B
\end{code}
%</usual-fold>

\begin{code}
module foldr-fake where
\end{code}
%<*foldr-sum>
\begin{code}
  sum′ : ∀ A → List A → (A → ℕ) → ℕ
  sum′ = foldr {X = λ A → (A → ℕ) → ℕ} go
    where
    go : ∀ A → ⊤ ⊎ (A × ((A → ℕ) → ℕ)) → (A → ℕ) → ℕ
    go A (inj₁ tt)        f = zero
    go A (inj₂ (x , xs))  f = f x + xs f

  sum : List ℕ → ℕ
  sum xs = sum′ ℕ xs id 
\end{code}
%</foldr-sum>


\begin{code}
module foldr′ where
  foldr' : ∀ {X} → ⟦ ListD ⟧D X ⇶ X → μ-ix ListD ⇶ X
  foldr' = fold {D = ListD}

  sum′ : μ-ix ListD ⇶ λ (_ , A) _ → (A → ℕ) → ℕ
  sum′ = foldr' go
    where
    go : ⟦ ListD ⟧D (λ z _ → (z .snd → ℕ) → ℕ) ⇶ (λ z _ → (z .snd → ℕ) → ℕ)
    go p _ (inj₁ x) = const zero
    go p _ (inj₂ (inj₁ (x , f , _))) y = y x + f y

  sum : {A : Type} → (A → ℕ) → μ-ix ListD (_ , A) _ → ℕ
  sum {A = A} f x = sum′ (tt , A) tt x f 

  list-123 : μ-ix ListD (_ , ℕ) _
  list-123 = con (inj₂ (inj₁ (suc zero , con (inj₂ (inj₁ (suc (suc zero) , con (inj₂ (inj₁ (suc (suc (suc zero)) , con (inj₁ refl) , refl))) , refl))) , refl)))
\end{code}

\begin{code}
private variable
  CD CE : Con-ix Γ V I
\end{code}

%<*hpty>
\begin{code}
_∼_ : {B : A → Type} → (f g : ∀ a → B a) → Type
f ∼ g = ∀ a → f a ≡ g a
\end{code}
%</hpty>

\begin{code}
infix 0 _∼_

private variable
  re-par : Cxf Δ Γ
  re-var : Vxf {Δ = Δ} {Γ = Γ} re-par W V
  re-index : J → I
\end{code}

\begin{code}
mutual
\end{code}
%<*Orn>
\begin{code}
  data  Orn (re-par : Cxf Δ Γ) (re-index : J → I) :
        U-ix Γ I → U-ix Δ J → Type where
      []   : Orn re-par re-index [] []
      _∷_  : ConOrn re-par id re-index CD CE
           → Orn re-par re-index D E
           → Orn re-par re-index (CD ∷ D) (CE ∷ E)  
\end{code}
%</Orn>


%<*ConOrn>
\begin{code}
  data ConOrn (re-par : Cxf Δ Γ) (re-var : Vxf re-par W V) (re-index : J → I) :
              Con-ix Γ V I → Con-ix Δ W J → Type where
    𝟙  : ∀ {i j}
       → re-index ∘ j ∼ i ∘ var→par re-var
       → ConOrn re-par re-var re-index (𝟙 i) (𝟙 j)

    ρ  : ∀ {i j CD CE}
       → re-index ∘ j ∼ i ∘ var→par re-var
       → ConOrn re-par re-var re-index CD CE
       → ConOrn re-par re-var re-index (ρ i CD) (ρ j CE)

    σ  : ∀ {S CD CE}
       → ConOrn re-par (Vxf-▷ re-var S) re-index CD CE
       → ConOrn re-par re-var re-index (σ S CD) (σ (S ∘ var→par re-var) CE)

    Δσ  : ∀ {S CD CE}
        → ConOrn re-par (re-var ∘ fst) re-index CD CE
        → ConOrn re-par re-var re-index CD (σ S CE)
\end{code}
%</ConOrn>

%<*NatD-ListD>
\begin{code}
NatD-ListD : Orn ! id NatD ListD
NatD-ListD  = 𝟙 (const refl)
            ∷ Δσ {S = λ { ((_ , A), _) → A }}
            ( ρ (const refl)
            ( 𝟙 (const refl)))
            ∷ []
\end{code}
%</NatD-ListD>

%<*ListD-VecD>
\begin{code}
ListD-VecD : Orn id ! ListD VecD
ListD-VecD  = 𝟙 (const refl)
            ∷ Δσ {S = λ _ → ℕ}
            ( σ
            ( ρ {j = λ { (_ , (_ , n) , _) → n }}      (const refl)
            ( 𝟙 {j = λ { (_ , (_ , n) , _) → suc n }}  (const refl))))
            ∷ []
\end{code}
%</ListD-VecD>

%<*bimap>
\begin{code}
bimap  : {A B C D E : Type}
       → (A → B → C) → (D → A) → (E → B)
       → D → E → C
bimap f g h d e = f (g d) (h e)
\end{code}
%</bimap>

\begin{code}
mutual
\end{code}
%<*ornErase>
\begin{code}
  ornErase  : ∀ {re-par re-index} {X}
            → Orn re-par re-index D E
            →  ⟦ E ⟧D (bimap X re-par re-index)
               ⇶ bimap (⟦ D ⟧D X) re-par re-index
  ornErase (CD ∷ D) p j (inj₁ x) = inj₁ (conOrnErase CD (p , tt) j x)
  ornErase (CD ∷ D) p j (inj₂ x) = inj₂ (ornErase D p j x)

  conOrnErase  : ∀  {re-par re-index} {W V} {X} {re-var : Vxf re-par W V}
                   {CD : Con-ix Γ V I} {CE : Con-ix Δ W J}
               → ConOrn re-par re-var re-index CD CE
               →  ⟦ CE ⟧C (bimap X re-par re-index)
                  ⇶ bimap (⟦ CD ⟧C X) (var→par re-var) re-index
  conOrnErase {re-index = i} (𝟙 sq) p j x    = trans (cong i x) (sq p)
  conOrnErase {X = X} (ρ sq CD) p j (x , y)  = subst (X _) (sq p) x
                                             , conOrnErase CD p j y
  conOrnErase (σ CD) (p , w) j (s , x)       = s
                                             , conOrnErase CD (p , w , s) j x
  conOrnErase (Δσ CD) (p , w) j (s , x)      = conOrnErase CD (p , w , s) j x
\end{code}
%</ornErase> 



%<*ornAlg>
\begin{code}
ornAlg  : ∀ {D : U-ix Γ I} {E : U-ix Δ J} {re-par re-index}
        → Orn re-par re-index D E
        →  ⟦ E ⟧D (bimap (μ-ix D) re-par re-index)
           ⇶ bimap (μ-ix D) re-par re-index
ornAlg O p j x = con (ornErase O p j x)
\end{code}
%</ornAlg>

%<*ornForget-type>
\begin{code}
ornForget  : ∀ {re-par re-index} → Orn re-par re-index D E
           → μ-ix E ⇶ bimap (μ-ix D) re-par re-index 
\end{code}
%</ornForget-type>

%<*ornForget>
\begin{code}
ornForget O = fold (ornAlg O)
\end{code}
%</ornForget>

\begin{code}
mutual
\end{code}

%<*OrnDesc>
\begin{code}
  data  OrnDesc (Δ : Tel ⊤) (J : Type)
        (re-par : Cxf Δ Γ) (re-index : J → I)
        : U-ix Γ I → Type where
    []   : OrnDesc Δ J re-par re-index []
    _∷_  : ConOrnDesc Δ ∅ J re-par ! re-index CD
         → OrnDesc Δ J re-par re-index D
         → OrnDesc Δ J re-par re-index (CD ∷ D)
\end{code}
%</OrnDesc>

%<*ConOrnDesc>
\begin{code}
  data ConOrnDesc  (Δ : Tel ⊤) (W : ExTel Δ) (J : Type)
                   (re-par : Cxf Δ Γ) (re-var : Vxf re-par W V) (re-index : J → I)
                   : Con-ix Γ V I → Type where  
    𝟙  : ∀ {i} (j : W ⊢ J)
       → re-index ∘ j ∼ i ∘ var→par re-var
       → ConOrnDesc Δ W J re-par re-var re-index (𝟙 i)

    ρ  : ∀ {i} {CD} (j : W ⊢ J)
       → re-index ∘ j ∼ i ∘ var→par re-var
       → ConOrnDesc Δ W J re-par re-var re-index CD
       → ConOrnDesc Δ W J re-par re-var re-index (ρ i CD)

    σ  : ∀ (S : V ⊢ Type) {CD}
       → ConOrnDesc Δ (W ▷ S ∘ var→par re-var) J re-par (Vxf-▷ re-var S) re-index CD
       → ConOrnDesc Δ W J re-par re-var re-index (σ S CD)

    Δσ  : ∀ (S : W ⊢ Type) {CD}
        → ConOrnDesc Δ (W ▷ S) J re-par (re-var ∘ fst) re-index CD
        → ConOrnDesc Δ W J re-par re-var re-index CD
\end{code}
%</ConOrnDesc>

%<*NatOD>
\begin{code}
NatOD : OrnDesc (∅ ▷ const Type) ⊤ ! ! NatD
NatOD  = 𝟙 (λ _ → tt) (λ a → refl)
       ∷ Δσ (λ { ((_ , A) , _) → A })
       ( ρ (λ _ → tt) (λ a → refl)
       ( 𝟙 (λ _ → tt) (λ a → refl)) )
       ∷ []
\end{code}
%</NatOD>

\begin{code}
mutual
\end{code}

%<*toDesc>
\begin{code}
  toDesc  : {D : U-ix Γ I} → OrnDesc Δ J re-par re-index D
          → U-ix Δ J
  toDesc []         = []
  toDesc (COD ∷ OD) = toCon COD ∷ toDesc OD

  toCon  : ∀ {CD : Con-ix Γ V I} {re-par} {W} {re-var : Vxf re-par W V}
         → ConOrnDesc Δ W J re-par re-var re-index CD
         → Con-ix Δ W J
  toCon (𝟙 j j∼i)               = 𝟙 j
  toCon (ρ j j∼i COD)           = ρ j (toCon COD)
  toCon {re-var = v} (σ S COD)  = σ (S ∘ var→par v) (toCon COD)
  toCon (Δσ S COD)              = σ S (toCon COD)
\end{code}
%</toDesc>

\begin{code}
mutual
\end{code}
%<*toOrn>
\begin{code}
  toOrn  :  {D : U-ix Γ I}
            (OD : OrnDesc Δ J re-par re-index D)
         →  Orn re-par re-index D (toDesc OD)
  toOrn []         = []
  toOrn (COD ∷ OD) = toConOrn COD ∷ toOrn OD

  toConOrn :  ∀ {CD : Con-ix Γ V I} {re-par} {W} {re-var : Vxf re-par W V}
           →  (COD : ConOrnDesc Δ W J re-par re-var re-index CD)
           →  ConOrn re-par re-var re-index CD (toCon COD)
  toConOrn (𝟙 j j∼i)               = 𝟙 j∼i
  toConOrn (ρ j j∼i COD)           = ρ j∼i  (toConOrn COD)
  toConOrn (σ S COD)               = σ      (toConOrn COD)
  toConOrn (Δσ S COD)              = Δσ     (toConOrn COD)
\end{code}
%</toOrn>
\end{document}
