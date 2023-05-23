{-# OPTIONS --safe #-}

module Temporary.Desc where

open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Data.Unit.Polymorphic
open import Data.Product
open import Data.Nat
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J)

infixl 10 _▷_

private variable
  a b c : Level
  I J : Type a
  A B C : Type a

levelOf : ∀ {a} → Type a → Level
levelOf {a} _ = a

data Tel : Typeω
levelOfTel : Tel → Level
⟦_⟧tel : (Γ : Tel) → Type (levelOfTel Γ)

data Tel where
  ∅   : Tel
  _▷_ : ∀ {a} (Γ : Tel) (S : ⟦ Γ ⟧tel → Type a) → Tel

private variable
  Γ Δ : Tel

levelOfTel ∅             = ℓ-zero
levelOfTel (_▷_ {a} Γ S) = ℓ-max a (levelOfTel Γ) 

⟦ ∅     ⟧tel = ⊤
⟦ Γ ▷ S ⟧tel = Σ ⟦ Γ ⟧tel S 

data Desc (I : Type a) : Tel → Typeω

Cxf : (Γ Δ : Tel) → Type (ℓ-max (levelOfTel Γ) (levelOfTel Δ))
Cxf Γ Δ = ⟦ Γ ⟧tel → ⟦ Δ ⟧tel

mapTel : (f : Cxf Γ Δ) (S : ⟦ Δ ⟧tel → Type a) (h : ∀ x → S x → S x) → Cxf (Γ ▷ (S ∘ f)) (Δ ▷ S)
mapTel f S h (ps , p) = f ps , h (f ps) p

levelOfDesc : Desc I Γ → Level

data μ (D : Desc I Γ) (i : I) (ps : ⟦ Γ ⟧tel) : Type (levelOfDesc D) where

data Desc I where
  𝟙   : I → Desc I Γ

  σf : (S : ⟦ Γ ⟧tel → Type b) → Desc I (Γ ▷ S) → Desc I Γ
  σd : (j : J) (f : Cxf Γ Δ) (D : Desc J Δ) → Desc I (Γ ▷ (μ D j ∘ f)) → Desc I Γ

  σf′ : (S : ⟦ Γ ⟧tel → Type b) → Desc I Γ → Desc I Γ
  σd′ : (j : J) (f : Cxf Γ Δ) (D : Desc J Δ) → Desc I Γ → Desc I Γ

  rec : I → (Cxf Γ Γ) → Desc I Γ → Desc I Γ


-- convert : (S : ⟦ Γ ⟧tel → Type b) → (∀ x → S x → Desc I Γ) → Desc I (Γ ▷ S)
-- should be uninhabited! it would let constructors determine parameters

-- straight from effectfully
_⊕_ : Desc I Γ → Desc I Γ → Desc I Γ
D ⊕ E = {!\sigm!}

levelOfDesc {I = I} (𝟙 _) = levelOf I
levelOfDesc (σf {b = b} S D) = ℓ-max b (levelOfDesc D)
levelOfDesc (σf′ {b = b} S D) = ℓ-max b (levelOfDesc D)
levelOfDesc (σd j f R D) = ℓ-max (levelOfDesc R) (levelOfDesc D)
levelOfDesc (σd′ j f R D) = ℓ-max (levelOfDesc R) (levelOfDesc D)
levelOfDesc (rec i f D) = levelOfDesc D

{-
first : {C : B → Type b} (f : A → B) → Σ A (C ∘ f) → Σ B C
first f (b , c) = f b , c
-}

{-
data Thin : Tel → Tel → Typeω 
thin : Thin Γ Δ → Cxf Γ Δ
data Thin where
  refl : Thin Γ Γ
  keep : (S : ⟦ Δ ⟧tel → Type b) (t : Thin Γ Δ) → Thin (Γ ▷ (S ∘ thin t)) (Δ ▷ S)
  drop : (S : ⟦ Γ ⟧tel → Type b) → Thin Γ Δ → Thin (Γ ▷ S) Δ

thin refl = id
thin (keep S t) (g , s) = thin t g , s
thin (drop S t) (g , s) = thin t g

liftThin : Thin Γ Δ → Cxf Δ Δ → Cxf Γ Γ
liftThin refl f = id
liftThin (keep S t) f (g , s) = ({!!} , {!!})
liftThin (drop S t) f (g , s) = liftThin t f g , {!!}

precomp : Thin Γ Δ → Desc I Δ → Desc I Γ
precomp f (𝟙 x) = 𝟙 x
precomp f (σf S D) = σf (S ∘ (thin f)) (precomp (keep S f)  D)
precomp f (σd j g R D) = σd j (g ∘ thin f) R (precomp (keep _ f) D)
precomp f (rec i g D) = rec i (liftThin f g) (precomp f D) 
-}

{-
data Poke : Tel → Typeω
bumped : Poke Γ → Tel
data Poke where
  here  : (Γ : Tel) (S : ⟦ Γ ⟧tel → Type b) → Poke Γ
  there : (p : Poke Γ) (S : ⟦ Γ ⟧tel → Type b) → Poke (Γ ▷ S)

prebump : (p : Poke Γ) → (⟦ Γ ⟧tel → A) → ⟦ bumped p ⟧tel → A

bumped-1 : Poke Γ → Tel
bumped-l : Poke Γ → Level
bumped-2 : (p : Poke Γ) → (⟦ bumped-1 p ⟧tel → Type (bumped-l p))

bumped-l (here {b = b} _ S) = b
bumped-l (there {b = b} p S) = b

bumped-1 (here Γ S) = Γ
bumped-1 (there p S) = bumped p

bumped-2 (here Γ S) = S
bumped-2 (there p S) = prebump p S 

bumped p = bumped-1 p ▷ bumped-2 p

debump : (p : Poke Γ) (S : ⟦ Γ ⟧tel → Type b) → Σ ⟦ bumped p ⟧tel (prebump p S) → Σ ⟦ Γ ⟧tel S
prebump (here _ S) f x = f (proj₁ x)
prebump (there p S) f x = f (debump p S x)

debump (here _ S) T x = (proj₁ (proj₁ x)) , (proj₂ x)
debump (there p S) T x = debump p _ (proj₁ x) , proj₂ x

bump : (p : Poke Γ) → Desc I Γ → Desc I (bumped p)
bump (here _ S) (𝟙 x) = 𝟙 x
bump (here _ S) (σf T D) = σf (T ∘ proj₁) (bump (there (here _ _) T) D)
bump (here _ S) (σd j f R D) = σd j (f ∘ proj₁) R (bump (there (here _ _) (μ R j ∘ f)) D)
bump (here _ S) (rec i f D) = rec i {!!} {!!}
bump (there p S) D = {!!}
-}

open import Level using (Lift)

⟦_⟧Desc : (D : Desc I Γ) → ∀ {c}
        → (I → ⟦ Γ ⟧tel → Type (ℓ-max c (levelOfDesc D)))
        → (I → ⟦ Γ ⟧tel → Type (ℓ-max c (levelOfDesc D)))
⟦ 𝟙 j ⟧Desc {c = c} X i p = Lift c (i ≡ j) 
⟦ σf {b = b} S D ⟧Desc {c = c} X i p = Σ[ s ∈ S p ] ⟦ D ⟧Desc {c = ℓ-max b c} (λ i p → X i (proj₁ p)) i (p , s) 
⟦ σd j f R D ⟧Desc {c = c} X i p = Σ[ r ∈ μ R j (f p) ] ⟦ D ⟧Desc {c = ℓ-max (levelOfDesc D) (ℓ-max (levelOfDesc R) c)} (λ i p → X i (proj₁ p)) i (p , r)
⟦ σf′ {b = b} S D ⟧Desc {c = c} X i p = S p × ⟦ D ⟧Desc {c = ℓ-max b c} X i p 
⟦ σd′ j f R D ⟧Desc {c = c} X i p = μ R j (f p) × ⟦ D ⟧Desc {c = ℓ-max (levelOfDesc D) (ℓ-max (levelOfDesc R) c)} X i p
⟦ rec j f D ⟧Desc X i p = X i (f p)


-- {-
-- data ConOrn (e : J → I) (f : Cxf Δ Γ) : ConDesc I Γ → ConDesc I Δ → Typeω where
--   𝟙  : ConOrn e f 𝟙 𝟙
--   σf :  
-- -}

-- {-
-- data ConOrn {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) : ConDesc I Γ → Typeω where
--   𝟙  : ConOrn J e Δ f 𝟙
--   σf : (S : ⟦ Γ ⟧tel → Type a) {D : ConDesc I (Γ ▷ S)} (O : ConOrn J e (Δ ▷ (S ∘ f)) (map f id) D) → ConOrn J e Δ f (fld S ⊗ D)
--   Δf : (T : ⟦ Δ ⟧tel → Type a) {D : ConDesc I Γ} (O : ConOrn J e Δ f D) → ConOrn J e Δ f D
--   --          ^ huh

--   -- ...

-- data ROrn {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) : RDesc I Γ → Typeω where
--   𝟘   : ROrn J e Δ f 𝟘
--   _⊕_ : {C : ConDesc I Γ} {D : RDesc I Γ} → ConOrn J e Δ f C → ROrn J e Δ f D → ROrn J e Δ f (C ⊕ D)

-- data Inv {A : Type a} {B : Type b} (f : A → B) : B → Type (ℓ-max a b) where
--   ok : ∀ x → Inv f (f x)

-- Orn : {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) → Desc I Γ → Typeω
-- Orn {I} J e Δ f D = ∀ {i} → (j : Inv e i) → ROrn J e Δ f (D i)
-- -}
