module Ornament.OrnL where

open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Data.Unit.Polymorphic
open import Data.Empty.Polymorphic
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J)
open import Level using (Lift)

open import Ornament.DescL

private variable
  a b c d z w : Level
  I J K : Type a
  A B C : Type a
  Γ Δ Θ : Tel a 


-- ornaments
fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ A λ x → f x ≡ y

data Orn {I : Type z} {J : Type w} {Γ : Tel c} {Δ : Tel d} (e : J → I) (f : Cxf Δ Γ) : Desc I Γ a → Desc J Δ b → Typeω
data ConOrn (e : J → I) (f : Cxf Δ Γ) : Con I Γ a → Con J Δ b → Typeω where
  -- preserving
  𝟙   : ∀ {i j} → (∀ x → e (j x) ≡ i (f x)) → ConOrn e f (𝟙 i) (𝟙 j)
  σf  : {S : ⟦ Γ ⟧tel → Type a} {D : Con I (Γ ▷ S) a} {E : Con J (Δ ▷ (S ∘ f)) b} → ConOrn e (Cxf-both f S) D E → ConOrn e f (σf S D) (σf (S ∘ f) E)
  σf′ : {S : ⟦ Γ ⟧tel → Type a} {D : Con I Γ a} {E : Con J Δ b} → ConOrn e f D E → ConOrn e f (σf′ S D) (σf′ (S ∘ f) E)
  σd  : {j : ⟦ Γ ⟧tel → K} {g : Cxf Γ Θ} {R : Desc K Θ c} {D : Con I _ a} {E : Con J _ b} → ConOrn e (Cxf-both f (λ x → μ R (g x) (j x))) D E → ConOrn e f (σd j g R D) (σd (j ∘ f) (g ∘ f) R E)
  σd′ : {j : ⟦ Γ ⟧tel → K} {g : Cxf Γ Θ} {R : Desc K Θ c} {D : Con I _ a} {E : Con J _ b} → ConOrn e f D E → ConOrn e f (σd′ j g R D) (σd′ (j ∘ f) (g ∘ f) R E)
  rec : ∀ {j} {k} {g} {h} {D : Con I _ a} {E : Con J _ b} → (∀ x → e (k x) ≡ j (f x)) → (∀ x → f (h x) ≡ g (f x)) → ConOrn e f D E → ConOrn e f (rec j g D) (rec k h E) 

  -- extending
  

  -- deleting

  -- re-indexing


data Orn {I = I} {J = J} {Γ = Γ} {Δ = Δ} e f where
  []  : Orn e f ([] {c = a}) ([] {c = b})
  _∷_ : {D : Con I Γ a} {E : Con J Δ b} {Ds : Desc I Γ c} {Es : Desc J Δ d} → ConOrn e f D E → Orn {I = I} {J = J} {Γ = Γ} {Δ = Δ} e f Ds Es → Orn e f (D ∷ Ds) (E ∷ Es)


-- ornamental descriptions
data OrnDesc {Δ : Tel z} {I : Type b} {J : Type d} {Γ : Tel c} (e : J → I) (f : Cxf Δ Γ) : Desc I Γ a → Level → Typeω
data ConOrnDesc (e : J → I) (f : Cxf Δ Γ) : Con I Γ a → Level → Typeω where
  𝟙   : {i : ⟦ Γ ⟧tel → I} → (j : ∀ x → fiber e (i (f x))) → ConOrnDesc e f (𝟙 i) (levelOf J)
  σf  : {S : ⟦ Γ ⟧tel → Type a} {D : Con I (Γ ▷ S) a} → ConOrnDesc e (Cxf-both f S) D b → ConOrnDesc e f (σf S D) (ℓ-max a b)
  σf′ : {S : ⟦ Γ ⟧tel → Type a} {D : Con I Γ a} → ConOrnDesc e f D b → ConOrnDesc e f (σf′ S D) (ℓ-max a b)

  -- the presence of this constructor makes (*)
  σd  : {j : ⟦ Γ ⟧tel → K} {g : Cxf Γ Θ} {R : Desc K Θ b} {D : Con I (Γ ▷ (λ v → μ R (g v) (j v))) a} → ConOrnDesc e (Cxf-both f (λ x → μ R (g x) (j x))) D c → ConOrnDesc e f (σd j g R D) (ℓ-max b (ℓ-max c (levelOf K)))


data OrnDesc {I = I} {Γ = Γ} e f where
  []  : OrnDesc e f ([] {c = a}) a
  _∷_ : {D : Con I Γ a} {Ds : Desc I Γ b} → ConOrnDesc e f D c → OrnDesc {I = I} {Γ = Γ} e f Ds d → OrnDesc e f (D ∷ Ds) (ℓ-max c d)


toDesc : {Γ : Tel a} {Δ : Tel b} {e : J → I} {f : Cxf Δ Γ} {D : Con I Γ c} → ConOrnDesc e f D d → Con J Δ d
-- (*) this case gets stuck in unification when the σd case is missing?
toDesc (𝟙 j)    = 𝟙 (proj₁ ∘ j)
toDesc (σf  OD) = σf _ (toDesc OD) 
toDesc {f = f} (σf′ {S = S} OD) = σf′ (S ∘ f) (toDesc OD)
toDesc (σd OD) = σd _ _ _ (toDesc OD)

-- but why? σd doesn't look like 𝟙, does it?

toOrn : {Γ : Tel a} {Δ : Tel b} {e : J → I} {f : Cxf Δ Γ} {D : Con I Γ c} → (OD : ConOrnDesc e f D d) → ConOrn e f D (toDesc OD)
toOrn (𝟙 j)    = 𝟙 (proj₂ ∘ j)
toOrn (σf  OD) = σf (toOrn OD)
toOrn (σf′ OD) = σf′ (toOrn OD)
toOrn (σd  OD) = σd (toOrn OD) 


{-
data ConOrn {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) : ConDesc I Γ → Typeω where
  𝟙  : ConOrn J e Δ f 𝟙
  σf : (S : ⟦ Γ ⟧tel → Type a) {D : ConDesc I (Γ ▷ S)} (O : ConOrn J e (Δ ▷ (S ∘ f)) (map f id) D) → ConOrn J e Δ f (fld S ⊗ D)
  Δf : (T : ⟦ Δ ⟧tel → Type a) {D : ConDesc I Γ} (O : ConOrn J e Δ f D) → ConOrn J e Δ f D
  --          ^ huh

  -- ...

data ROrn {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) : RDesc I Γ → Typeω where
  𝟘   : ROrn J e Δ f 𝟘
  _⊕_ : {C : ConDesc I Γ} {D : RDesc I Γ} → ConOrn J e Δ f C → ROrn J e Δ f D → ROrn J e Δ f (C ⊕ D)

data Inv {A : Type a} {B : Type b} (f : A → B) : B → Type (ℓ-max a b) where
  ok : ∀ x → Inv f (f x)

Orn : {I : Type a} {Γ : Tel} (J : Type b) (e : J → I) (Δ : Tel) (f : Cxf Δ Γ) → Desc I Γ → Typeω
Orn {I} J e Δ f D = ∀ {i} → (j : Inv e i) → ROrn J e Δ f (D i)
-}
