{-# OPTIONS --without-K #-}

open import Data.Sum using (_⊎_; inj₁; inj₂)

module ProgOrn.Ornaments where

open import Function using (const; _∘_; case_of_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; <_,_>; uncurry; _×_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)


open import Level renaming (zero to lzero; suc to lsuc)

private variable
  ℓ ℓ′ ℓ″ : Level

--------
-- Datatype descriptions

data RDesc (I : Set ℓ) : Set (lsuc ℓ) where
  ṿ   : (is : List I) → RDesc I
  σ   : (S : Set) (D : S → RDesc I) → RDesc I

syntax σ S (λ s → D) = σ[ s ∈ S ] D

_σ′_ : ∀ {I : Set ℓ} → Set → RDesc I → RDesc I
S σ′ D = σ[ _ ∈ S ] D

infixr 10 _σ′_

Desc : Set ℓ → Set (lsuc ℓ)
Desc I = I → RDesc I

Ṗ : {I : Set ℓ} → List I → (I → Set ℓ′) → Set ℓ′
Ṗ []       X = Lift _ ⊤
Ṗ (i ∷ is) X = X i × Ṗ is X

⟦_⟧ : {I : Set ℓ} → RDesc I → (I → Set ℓ′) → Set ℓ′
⟦ ṿ is  ⟧ X = Ṗ is X
⟦ σ S D ⟧ X = Σ[ s ∈ S ] ⟦ D s ⟧ X

Ḟ : {I : Set ℓ} → Desc I → (I → Set ℓ′) → (I → Set ℓ′)
Ḟ D X i = ⟦ D i ⟧ X

_⇉_ : {I : Set ℓ} → (I → Set ℓ′) → (I → Set ℓ″) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
X ⇉ Y = ∀ {i} → X i → Y i

data μ {I : Set ℓ} (D : Desc I) : I → Set ℓ where
  con : Ḟ D (μ D) ⇉ μ D

data ListTag : Set where
  ‘nil  : ListTag
  ‘cons : ListTag

NatD : Desc ⊤
NatD tt = σ ListTag λ { ‘nil  → ṿ []
                      ; ‘cons → ṿ (tt ∷ []) }

ListD : Set → Desc ⊤
ListD A tt = σ ListTag λ { ‘nil  → ṿ []
                         ; ‘cons → σ[ _ ∈ A ] ṿ (tt ∷ []) }

VecD : Set → Desc ℕ
VecD A zero    = ṿ []
VecD A (suc n) = σ[ _ ∈ A ] ṿ (n ∷ [])

data ConMenu : Set where
  ‘always  : ConMenu
  ‘indexed : ConMenu

Fin'D : Desc ℕ
Fin'D n = σ ConMenu λ { ‘always  → ṿ []
                      ; ‘indexed → case n of λ { zero    → σ ⊥ λ ()
                                               ; (suc m) → ṿ (m ∷ []) } }

List' : Set → Set
List' A = μ (ListD A) tt

pattern []'       = con (‘nil  , _)
pattern _∷'_ a as = con (‘cons , a , as , _)

_++'_ : {A : Set} → List' A → List' A → List' A
[]'       ++' ys = ys
(x ∷' xs) ++' ys = x ∷' (xs ++' ys)

-- without-K kills the termination here
mutual
  {-# TERMINATING #-}
  fold : {I : Set} {D : Desc I} {X : I → Set} → Ḟ D X ⇉ X → μ D ⇉ X
  fold {D = D} f {i} (con ds) = f (mapFold (D i) f ds)

  mapFold : {I : Set} {D : Desc I} (D' : RDesc I) → {X : I → Set} → (Ḟ D X ⇉ X) → ⟦ D' ⟧ (μ D) → ⟦ D' ⟧ X
  mapFold (ṿ is)   f ds         = mapFold-Ṗ f is ds
  mapFold (σ S D') f (s , ds)   = s , mapFold (D' s) f ds

  mapFold-Ṗ : {I : Set} {D : Desc I} {X : I → Set} → (Ḟ D X ⇉ X) → (is : List I) → Ṗ is (μ D) → Ṗ is X
  mapFold-Ṗ f []       _        = _
  mapFold-Ṗ f (i ∷ is) (d , ds) = fold f d , mapFold-Ṗ f is ds

--------
-- Ornaments

data Inv {A : Set ℓ} {B : Set ℓ′} (f : A → B) : B → Set (ℓ ⊔ ℓ′) where
  ok : (x : A) → Inv f (f x)

und : {A : Set ℓ} {B : Set ℓ′} {f : A → B} {y : B} → Inv f y → A
und (ok x) = x

data Ė {I : Set ℓ} {J : Set ℓ′} (e : J → I) : List J → List I → Set (ℓ ⊔ ℓ′) where
  []  : Ė e [] []
  _∷_ : {j : J} {i : I} (eq : e j ≡ i) {js : List J} {is : List I} (eqs : Ė e js is) → Ė e (j ∷ js) (i ∷ is)

data ROrn {I : Set ℓ} {J : Set ℓ′} (e : J → I) : RDesc I → RDesc J → Set (lsuc ℓ ⊔ lsuc ℓ′) where
  ṿ   : {js : List J} {is : List I} (eqs : Ė e js is) → ROrn e (ṿ is) (ṿ js)
  σ   : (S : Set) {D : S → RDesc I} {E : S → RDesc J} (O : (s : S) → ROrn e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ   : (T : Set) {D : RDesc I} {E : T → RDesc J} (O : (t : T) → ROrn e D (E t)) → ROrn e D (σ T E)
  ∇   : {S : Set} (s : S) {D : S → RDesc I} {E : RDesc J} (O : ROrn e (D s) E) → ROrn e (σ S D) E

syntax Δ T (λ t → O) = Δ[ t ∈ T ] O

Orn : {I : Set ℓ} {J : Set ℓ′} (e : J → I) (D : Desc I) (E : Desc J) → Set (lsuc ℓ ⊔ lsuc ℓ′)
Orn {I = I} e D E = {i : I} (j : Inv e i) → ROrn e (D i) (E (und j))

erase : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → {X : I → Set} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
erase (ṿ []          ) _        = _
erase (ṿ (refl ∷ eqs)) (x , xs) = x , erase (ṿ eqs) xs
erase (σ S O)          (s , xs) = s , erase (O s) xs
erase (Δ T O)          (t , xs) = erase (O t) xs
erase (∇ s O)          xs       = s , erase O xs

ornAlg : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → Ḟ E (μ D ∘ e) ⇉ (μ D ∘ e)
ornAlg O {j} = con ∘ erase (O (ok j))

ornForget : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → μ E ⇉ (μ D ∘ e)
ornForget {E = E} O = fold (ornAlg {E = E} O)

! : {A : Set ℓ} → A → ⊤
! _ = tt

NatD-ListD : (A : Set) → Orn ! NatD (ListD A)
NatD-ListD A (ok tt) = σ ListTag λ { ‘nil  → ṿ []
                                   ; ‘cons → Δ[ _ ∈ A ] ṿ (refl ∷ []) }

ListD-VecD : (A : Set) → Orn ! (ListD A) (VecD A)
ListD-VecD A (ok zero   ) = ∇ ‘nil  (ṿ [])
ListD-VecD A (ok (suc n)) = ∇ ‘cons (σ[ _ ∈ A ] ṿ (refl ∷ []))


--------
-- Ornamental descriptions

data ROrnDesc {I : Set ℓ} (J : Set ℓ′) (e : J → I) : RDesc I → Set (lsuc ℓ ⊔ ℓ′) where
  ṿ   : {is : List I} (js : Ṗ is (Inv e)) → ROrnDesc J e (ṿ is)
  σ   : (S : Set) {D : S → RDesc I} (O : (s : S) → ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  Δ   : (T : Set) {D : RDesc I} (O : T → ROrnDesc J e D) → ROrnDesc J e D
  ∇   : {S : Set} (s : S) {D : S → RDesc I} (O : ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)

OrnDesc : {I : Set ℓ} (J : Set ℓ′) (e : J → I) (D : Desc I) → Set (lsuc ℓ ⊔ ℓ′)
OrnDesc {I = I} J e D = {i : I} (j : Inv e i) → ROrnDesc J e (D i)

Ṗ-toList : {I : Set ℓ} {J : Set ℓ′} {X : I → Set ℓ″} → (X ⇉ const J) → (is : List I) → Ṗ is X → List J
Ṗ-toList f []        _         = []
Ṗ-toList f (i ∷ is)  (x , xs)  = f x ∷ Ṗ-toList f is xs

und-Ṗ : {I : Set ℓ} {J : Set ℓ′} {e : J → I} (is : List I) → Ṗ is (Inv e) → List J
und-Ṗ = Ṗ-toList und

toRDesc : {I : Set ℓ} {J : Set ℓ′} {e : J → I} {D : RDesc I} → ROrnDesc J e D → RDesc J
toRDesc (ṿ {is} js) = ṿ (und-Ṗ is js)
toRDesc (σ S O)     = σ[ s ∈ S ] toRDesc (O s)
toRDesc (Δ T O)     = σ[ t ∈ T ] toRDesc (O t)
toRDesc (∇ s O)     = toRDesc O

⌊_⌋ : {I : Set ℓ} {J : Set ℓ′} {e : J → I} {D : Desc I} → OrnDesc J e D → Desc J
⌊ O ⌋ j = toRDesc (O (ok j))

to≡ : {A : Set ℓ} {B : Set ℓ′} {f : A → B} {y : B} → (x : Inv f y) → f (und x) ≡ y
to≡ (ok x) = refl

to≡-Ṗ : {I : Set ℓ} {J : Set ℓ′} {e : J → I} (is : List I) (js : Ṗ is (Inv e)) → Ė e (und-Ṗ is js) is
to≡-Ṗ []       _        = []
to≡-Ṗ (i ∷ is) (j , js) = to≡ j ∷ to≡-Ṗ is js

toROrn : {I : Set ℓ} {J : Set ℓ′} {e : J → I} {D : RDesc I} → (O : ROrnDesc J e D) → ROrn e D (toRDesc O)
toROrn (ṿ js)  = ṿ (to≡-Ṗ _ js)
toROrn (σ S O) = σ[ s ∈ S ] toROrn (O s)
toROrn (Δ T O) = Δ[ t ∈ T ] toROrn (O t)
toROrn (∇ s O) = ∇ s (toROrn O)

⌈_⌉ : {I : Set ℓ} {J : Set ℓ′} {e : J → I} {D : Desc I} → (O : OrnDesc J e D) → Orn e D ⌊ O ⌋
⌈ O ⌉ (ok j) = toROrn (O (ok j))


--------
-- Parallel composition

from≡ : ∀ {A : Set ℓ} {B : Set ℓ′} (f : A → B) {x y} → f x ≡ y → Inv f y
from≡ f {x} refl = ok x

record _⋈_ {A B C : Set} (f : A → C) (g : B → C) : Set where
  constructor _,_
  field
    {c} : C
    a   : Inv f c
    b   : Inv g c

pull : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → C
pull = _⋈_.c

pc-Ė : {I J K : Set} {e : J → I} {f : K → I} {is : List I} {js : List J} {ks : List K} →
       Ė e js is → Ė f ks is → Ṗ is (Inv (pull {J} {K} {I} {e} {f}))
pc-Ė             []           []           = _
pc-Ė {e = e} {f} (eeq ∷ eeqs) (feq ∷ feqs) = ok (from≡ e eeq , from≡ f feq) , pc-Ė eeqs feqs

mutual

  pcROrn : ∀ {I J K} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K} → ROrn e D E → ROrn f D F → ROrnDesc (e ⋈ f) pull D
  pcROrn (ṿ eeqs) (ṿ feqs) = ṿ (pc-Ė eeqs feqs)
  pcROrn (ṿ eeqs) (Δ T P)  = Δ[ t ∈ T ] pcROrn (ṿ eeqs) (P t)
  pcROrn (σ S O)  (σ .S P) = σ[ s ∈ S ] pcROrn (O s) (P s)
  pcROrn (σ f O)  (Δ T P)  = Δ[ t ∈ T ] pcROrn (σ f O) (P t)
  pcROrn (σ S O)  (∇ s P)  = ∇ s (pcROrn (O s) P)
  pcROrn (Δ T O)  P        = Δ[ t ∈ T ] pcROrn (O t) P
  pcROrn (∇ s O)  (σ S P)  = ∇ s (pcROrn O (P s))
  pcROrn (∇ s O)  (Δ T P)  = Δ[ t ∈ T ] pcROrn (∇ s O) (P t)
  pcROrn (∇ s O)  (∇ s' P) = Δ (s ≡ s') (pcROrn-double∇ O P)

  pcROrn-double∇ : {I J K S : Set} {e : J → I} {f : K → I} {D : S → RDesc I} {E : RDesc J} {F : RDesc K} {s s' : S} →
                   ROrn e (D s) E → ROrn f (D s') F → s ≡ s' → ROrnDesc (e ⋈ f) pull (σ S D)
  pcROrn-double∇ {s = s} O P refl = ∇ s (pcROrn O P)

pcOrn : ∀ {I J K} {e : J → I} {f : K → I} {D E F} → Orn e D E → Orn f D F → OrnDesc (e ⋈ f) pull D
pcOrn {e = e} {f} {D} {E} {F} O P (ok (j , k)) = pcROrn (O j) (P k)


--------
-- Optimised predicates

und-from≡ : ∀ {A : Set ℓ} {B : Set ℓ′} (f : A → B) {x y} → (eq : f x ≡ y) → und (from≡ f eq) ≡ x
und-from≡ f refl = refl

π₁ : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → A
π₁ = und ∘ _⋈_.a

diff-Ė-l : ∀ {I J K} {e : J → I} {f : K → I} {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) → Ė π₁ (und-Ṗ is (pc-Ė eeqs feqs)) js
diff-Ė-l         []           _            = []
diff-Ė-l {e = e} (eeq ∷ eeqs) (feq ∷ feqs) = und-from≡ e eeq ∷ diff-Ė-l eeqs feqs

mutual

  diffROrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
               (O : ROrn e D E) (P : ROrn f D F) → ROrn π₁ E (toRDesc (pcROrn O P))
  diffROrn-l (ṿ eeqs) (ṿ feqs) = ṿ (diff-Ė-l eeqs feqs)
  diffROrn-l (ṿ eeqs) (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (ṿ eeqs) (P t)
  diffROrn-l (σ S O)  (σ .S P) = σ[ s ∈ S ] diffROrn-l (O s) (P s)
  diffROrn-l (σ S O)  (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (σ S O) (P t)
  diffROrn-l (σ S O)  (∇ s P)  = ∇ s (diffROrn-l (O s) P)
  diffROrn-l (Δ T O)  P        = σ[ t ∈ T ] diffROrn-l (O t) P
  diffROrn-l (∇ s O)  (σ S P)  = diffROrn-l O (P s)
  diffROrn-l (∇ s O)  (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (∇ s O) (P t)
  diffROrn-l (∇ s O)  (∇ s' P) = Δ (s ≡ s') (diffROrn-l-double∇ O P)

  diffROrn-l-double∇ : ∀ {I J K} {e : J → I} {f : K → I} {S} {D E F} {s s' : S} →
                       (O : ROrn e (D s) E) (P : ROrn f (D s') F) (eq : s ≡ s') →
                       ROrn π₁ E (toRDesc (pcROrn-double∇ {D = D} O P eq))
  diffROrn-l-double∇ O P refl = diffROrn-l O P

diffOrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
            (O : Orn e D E) (P : Orn f D F) → Orn π₁ E ⌊ pcOrn {E = E} {F} O P ⌋
diffOrn-l {e = e} {f} {D} {E} {F} O P (ok (j , k)) = diffROrn-l (O j) (P k)

Ṗ-map : {I : Set} {X Y : I → Set} → (X ⇉ Y) → (is : List I) → Ṗ is X → Ṗ is Y
Ṗ-map f []       _        = _
Ṗ-map f (i ∷ is) (x , xs) = f x , Ṗ-map f is xs

erode : {I : Set} (D : RDesc I) → {J : I → Set} → ⟦ D ⟧ J → ROrnDesc (Σ I J) proj₁ D
erode (ṿ is)  js         = ṿ (Ṗ-map (λ {i} j → ok (i , j)) is js)
erode (σ S D) (s , js)   = ∇ s (erode (D s) js)

singOrn : {I : Set} (D : Desc I) → OrnDesc (Σ I (μ D)) proj₁ D
singOrn D (ok (i , con ds)) = erode (D i) ds

OptP : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) {i : I} → Inv e i → μ D i → Set
OptP {D = D} {E} O j x = μ ⌊ pcOrn {E = E} {F = ⌊ singOrn D ⌋} O ⌈ singOrn D ⌉ ⌋ (j , (ok (_ , x)))

-------
-- Promotions and upgrades

record Promotion (X Y : Set) : Set₁ where
  field
    Predicate  : X → Set
    forget     : Y → X
    complement : (y : Y) → Predicate (forget y)
    promote    : (x : X) → Predicate x → Y
    coherence  : (x : X) (p : Predicate x) → forget (promote x p) ≡ x

ornProm : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} → Orn e D E → (j : J) → Promotion (μ D (e j)) (μ E j)
ornProm {e = e} {D} {E} O j = record
  { Predicate  = OptP {E = E} O (ok j)
  ; forget     = ornForget O
  ; complement = complement
  ; promote    = promote
  ; coherence  = coherence
  }
  where
    postulate  -- derived from the pullback property of parallel composition
      complement : (y : μ E j) → OptP {E = E} O (ok j) (ornForget O y)
      promote    : (x : μ D (e j)) → OptP {E = E} O (ok j) x → μ E j
      coherence  : (x : μ D (e j)) (com : OptP {E = E} O (ok j) x) → ornForget O (promote x com) ≡ x
      

record Upgrade (X Y : Set) : Set₁ where
  field
    Predicate  : X → Set
    Coherence  : X → Y → Set
    complement : (x : X) (y : Y) → Coherence x y → Predicate x
    promote    : (x : X) → Predicate x → Y
    coherence  : (x : X) (p : Predicate x) → Coherence x (promote x p)

toUpgrade : {X Y : Set} → Promotion X Y → Upgrade X Y
toUpgrade p = record
  { Predicate  = Promotion.Predicate p
  ; Coherence  = λ x y  → Promotion.forget p y ≡ x
  ; complement = λ {._ y refl  → Promotion.complement p y }
  ; promote    = Promotion.promote p
  ; coherence  = Promotion.coherence p }

_⇀_ : {X Y Z W : Set} → Promotion X Y → Upgrade Z W → Upgrade (X → Z) (Y → W)
_⇀_ {X} {Y} p u = record
  { Predicate  = λ f → (x : X) → Promotion.Predicate p x → Upgrade.Predicate u (f x)
  ; Coherence  = λ f g → (y : Y) → Upgrade.Coherence u (f (Promotion.forget p y)) (g y)
  ; complement = λ f g c x com → Upgrade.complement u (f x) (g (Promotion.promote p x com))
                                   (subst (λ x' → Upgrade.Coherence u (f x') (g (Promotion.promote p x com)))
                                          (Promotion.coherence p x com) (c (Promotion.promote p x com)))
  ; promote    = λ f com → uncurry (Upgrade.promote u) ∘ Product.map f (com _) ∘ < Promotion.forget p , Promotion.complement p >
  ; coherence  = λ f com y → Upgrade.coherence u (f (Promotion.forget p y)) (com (Promotion.forget p y) (Promotion.complement p y)) }

new : (I : Set) {X : Set} {Y : I → Set} (u : (i : I) → Upgrade X (Y i)) → Upgrade X ((i : I) → Y i)
new I u = record
  { Predicate  = λ x  → (i : I) → Upgrade.Predicate (u i) x
  ; Coherence  = λ x y → (i : I) → Upgrade.Coherence (u i) x (y i)
  ; complement = λ x y coh i → Upgrade.complement (u i) x (y i) (coh i)
  ; promote    = λ x com i → Upgrade.promote (u i) x (com i)
  ; coherence  = λ x com i → Upgrade.coherence (u i) x (com i) }

syntax new I (λ i → u) = ∀⁺[ i ∈ I ] u

new' : (I : Set) {X : Set} {Y : I → Set} (u : (i : I) → Upgrade X (Y i)) → Upgrade X ({i : I} → Y i)
new' I u = record
  { Predicate  = λ x  → {i : I} → Upgrade.Predicate (u i) x
  ; Coherence  = λ x y → {i : I} → Upgrade.Coherence (u i) x (y {i})
  ; complement = λ x y coh {i} → Upgrade.complement (u i) x (y {i}) (coh {i})
  ; promote    = λ x com {i} → Upgrade.promote (u i) x (com {i})
  ; coherence  = λ x com {i} → Upgrade.coherence (u i) x (com {i}) }

syntax new' I (λ i → u) = ∀⁺[[ i ∈ I ]] u

fromUpgrade : {X Y : Set} (u : Upgrade X Y) → Promotion X (Σ[ y ∈ Y ] Σ[ x ∈ X ] Upgrade.Coherence u x y)
fromUpgrade u = record
 { Predicate  = Upgrade.Predicate u
 ; forget     = proj₁ ∘ proj₂
 ; complement = λ { (y , x , coh) → Upgrade.complement u x y coh }
 ; promote    = λ x com → Upgrade.promote u x com , x , Upgrade.coherence u x com
 ; coherence  = λ _ _ → refl }


--------
-- McBride's instance searching technique (ICFP 2014)

if_then_else_ : {A B C : Set} → A ⊎ B → ({{_ : A}} → C) → ({{_ : B}} → C) → C
if inj₁ a then t else u = t {{a}}
if inj₂ b then t else u = u {{b}}

record Σᴵ (A : Set) (B : A → Set) : Set where
  constructor ⟨_⟩ 
  field
    fst     : A
    {{snd}} : B fst

infix 2 Σᴵ-syntax

Σᴵ-syntax : (A : Set) → (A → Set) → Set
Σᴵ-syntax = Σᴵ

syntax Σᴵ-syntax A (λ x → B) = Σᴵ[ x ∈ A ] B

data Maybe' {A : Set} (X : A → Set) : Maybe A → Set where
  just    : {a : A} → X a → Maybe' X (just a)
  nothing : Maybe' X nothing

MaybeP : {A B : Set} → Promotion A B → Promotion (Maybe A) (Maybe B)
MaybeP p = record
  { Predicate  = Maybe' (Promotion.Predicate p)
  ; forget     = Maybe.map (Promotion.forget p)
  ; complement = λ { nothing  → nothing
                   ; (just b) → just (Promotion.complement p b) }
  ; promote    = λ { nothing  _        → nothing
                   ; (just a) (just x) → just (Promotion.promote p a x) }
  ; coherence  = λ { nothing  _        → refl
                   ; (just a) (just x) → cong just (Promotion.coherence p a x) } }
