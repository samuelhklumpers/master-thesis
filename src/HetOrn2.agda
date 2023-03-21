{-# OPTIONS --cumulativity #-}

module HetOrn2 where

open import Prelude hiding (⌊_⌋)
open import Cubical.Data.Bool
open import Cubical.Data.List



data RDesc (I : Type ℓ) (ℓ′ : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  ṿ   : (is : List I) → RDesc I ℓ′
  σ   : (S : Type ℓ′) (D : S → RDesc I ℓ′) → RDesc I ℓ′
  ṗ   : RDesc I ℓ′ → RDesc I ℓ′

syntax σ S (λ s → D) = σ[ s ∈ S ] D

_σ′_ : ∀ {I : Type ℓ} → Type ℓ′ → RDesc I ℓ′ → RDesc I ℓ′
S σ′ D = σ[ _ ∈ S ] D

infixr 10 _σ′_

Desc : Type ℓ → (ℓ′ : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ′))
Desc I ℓ′ = I → RDesc I ℓ′

Ṗ : {I : Type ℓ} → List I → (I → Type ℓ′) → Type ℓ′
Ṗ []       X = ⊤
Ṗ (i ∷ is) X = X i × Ṗ is X

⟦_⟧ : {I : Type ℓ} → RDesc I ℓ′ → (I → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) → Type ℓ″ → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))
⟦ ṿ is  ⟧ X A = Ṗ is X
⟦ σ S D ⟧ X A = Σ[ s ∈ S ] ⟦ D s ⟧ X A
⟦ ṗ D ⟧   X A = A × ⟦ D ⟧ X A

Ḟ : {I : Type ℓ} → Desc I ℓ′ → (I → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) → Type ℓ″ → I → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))
Ḟ D X A i = ⟦ D i ⟧ X A

data μ {I : Type ℓ} (D : Desc I ℓ′) (A : Type ℓ″) : I → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″)) where
  con : ∀ {i} → Ḟ D (μ D A) A i → μ D A i


data Inv {A : Type ℓ} {B : Type ℓ′} (f : A → B) : B → Type (ℓ-max ℓ ℓ′) where
  ok : (x : A) → Inv f (f x)

und : {A : Type ℓ} {B : Type ℓ′} {f : A → B} {y : B} → Inv f y → A
und (ok x) = x

data Ė {I : Type ℓ} {J : Type ℓ′} (e : J → I) : List J → List I → Type (ℓ-max ℓ ℓ′) where
  []  : Ė e [] []
  _∷_ : {j : J} {i : I} (eq : e j ≡ i) {js : List {a = ℓ′} J} {is : List {a = ℓ} I} (eqs : Ė e js is) → Ė e (j ∷ js) (i ∷ is)

data ROrn {I : Type ℓ} {J : Type ℓ′} {ℓ″} (e : J → I) : RDesc I ℓ″ → RDesc J ℓ″ → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))) where
  ṿ   : {js : List {a = ℓ′} J} {is : List {a = ℓ} I} (eqs : Ė e js is) → ROrn e (ṿ is) (ṿ js)
  σ   : (S : Type ℓ″) {D : S → RDesc {ℓ = ℓ} I ℓ″} {E : S → RDesc {ℓ = ℓ′} J ℓ″} (O : (s : S) → ROrn {ℓ = ℓ} {ℓ′ = ℓ′} e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ   : (T : Type ℓ″) {D : RDesc {ℓ = ℓ} I ℓ″} {E : T → RDesc {ℓ = ℓ′} J ℓ″} (O : (t : T) → ROrn {ℓ = ℓ} {ℓ′ = ℓ′} e D (E t)) → ROrn e D (σ T E)
  ∇   : {S : Type ℓ″} (s : S) {D : S → RDesc {ℓ = ℓ} I ℓ″} {E : RDesc {ℓ = ℓ′} J ℓ″} (O : ROrn e (D s) E) → ROrn e (σ S D) E
  ṗ   : {D : RDesc {ℓ = ℓ} I ℓ″} {E : RDesc {ℓ = ℓ′} J ℓ″} (O : ROrn e D E) → ROrn e (ṗ D) E

syntax Δ T (λ t → O) = Δ[ t ∈ T ] O

Orn : {I : Type ℓ} {J : Type ℓ′} (e : J → I) (D : Desc I ℓ″) (E : Desc J ℓ″) → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ′ ℓ″)))
Orn {ℓ = ℓ} {ℓ′ = ℓ′} {I = I} e D E = {i : I} (j : Inv {ℓ = ℓ′} {ℓ′ = ℓ} e i) → ROrn {ℓ = ℓ} {ℓ′ = ℓ′} e (D i) (E (und j))

! : {A : Type ℓ} → A → ⊤
! _ = tt

data ROrnDesc {I : Type ℓ} (J : Type ℓ′) {ℓ″} (e : J → I) : RDesc I ℓ″ → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ′ (ℓ-suc ℓ″))) where
  ṿ   : {is : List {a = ℓ} I} (js : Ṗ is (Inv e)) → ROrnDesc J e (ṿ is)
  σ   : (S : Type ℓ″) {D : S → RDesc {ℓ = ℓ} I ℓ″} (O : (s : S) → ROrnDesc {ℓ = ℓ} {ℓ′ = ℓ′} J e (D s)) → ROrnDesc J e (σ S D)
  Δ   : (T : Type ℓ″) {D : RDesc {ℓ = ℓ} I ℓ″} (O : T → ROrnDesc J e D) → ROrnDesc J e D
  ∇   : {S : Type ℓ″} (s : S) {D : S → RDesc {ℓ = ℓ} I ℓ″} (O : ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  ṗ   : {D : RDesc {ℓ = ℓ} I ℓ″} (O : ROrnDesc J e D) → ROrnDesc J e (ṗ D)

OrnDesc : {I : Type ℓ} (J : Type ℓ′) (e : J → I) (D : Desc I ℓ″) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℓ′ (ℓ-suc ℓ″)))
OrnDesc {ℓ = ℓ} {ℓ′ = ℓ′}  {I = I} J e D = {i : I} (j : Inv {ℓ = ℓ′} {ℓ′ = ℓ} e i) → ROrnDesc {ℓ = ℓ} {ℓ′ = ℓ′} J e (D i)

Ṗ-toList : {I : Type ℓ} {J : Type ℓ′} {X : I → Type ℓ″} → (∀ {j} → X j → const J j) → (is : List I) → Ṗ is X → List J
Ṗ-toList f []        _         = []
Ṗ-toList f (i ∷ is)  (x , xs)  = f x ∷ Ṗ-toList f is xs

und-Ṗ : {I : Type ℓ} {J : Type ℓ′} {e : J → I} (is : List I) → Ṗ is (Inv e) → List J
und-Ṗ = Ṗ-toList und

toRDesc : {I : Type ℓ} {J : Type ℓ′} {e : J → I} {D : RDesc {ℓ = ℓ} I ℓ″} → ROrnDesc {ℓ′ = ℓ′} J e D → RDesc J ℓ″
toRDesc (ṿ {is} js) = ṿ (und-Ṗ is js)
toRDesc (σ S O)     = σ[ s ∈ S ] toRDesc (O s)
toRDesc (Δ T O)     = σ[ t ∈ T ] toRDesc (O t)
toRDesc (∇ s O)     = toRDesc O
toRDesc (ṗ D)       = ṗ (toRDesc D)

⌊_⌋ : {I : Type ℓ} {J : Type ℓ′} {e : J → I} {D : Desc {ℓ = ℓ} I ℓ″} → OrnDesc {ℓ′ = ℓ′} J e D → Desc J ℓ″
⌊ O ⌋ j = toRDesc (O (ok j))



ListD : Desc ⊤ ℓ-zero
ListD _ = σ Bool λ
  { false → ṿ []
  ; true  → ṗ (ṿ [ tt ]) }


HetO′ : (D : RDesc {ℓ = ℓ-zero} ⊤ ℓ-zero) (E : RDesc {ℓ = ℓ-zero} ⊤ ℓ-zero) (x : Ḟ (λ _ → D) (μ (λ _ → E) Type) Type tt) → ROrnDesc (μ (λ _ → E) Type tt) ! D
HetO′ (ṿ is) E x = ṿ (map-ṿ is x)
  where
  map-ṿ : (is : List ⊤) → Ṗ is (μ (λ _ → E) Type) → Ṗ is (Inv {ℓ = ℓ-suc ℓ-zero} {A = μ (λ _ → E) Type tt} (! {ℓ = ℓ-suc ℓ-zero}))
  map-ṿ []       _        = _
  map-ṿ (_ ∷ is) (x , xs) = ok x , map-ṿ is xs
HetO′ (σ S D) E (s , x) = ∇ s (HetO′ (D s) E x)
HetO′ (ṗ D) E (A , x) = Δ[ _ ∈ A ] ṗ (HetO′ D E x) 

HetO : (D : RDesc {ℓ = ℓ-zero} ⊤ ℓ-zero) → OrnDesc (μ (λ _ → D) Type tt) ! λ _ → D
HetO D (ok (con x)) = HetO′ D D x

HListD = ⌊ HetO (ListD tt) ⌋

List′ : Type ℓ → Type ℓ
List′ A = μ ListD A tt

HList : μ (λ _ → ListD tt) Type tt → Type₁
HList = μ HListD ⊤


cons : A → List′ A → List′ A
cons x xs = con (true , x , xs , _)

hcons : (A : Type) (As : List′ {ℓ = ℓ-suc ℓ-zero} Type) → A → HList As → HList (cons A As)
hcons A As x xs = con (x , _ , xs , _)

-- nice
