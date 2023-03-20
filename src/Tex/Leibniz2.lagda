\begin{code}
{-# OPTIONS --cumulativity #-}

module Tex.Leibniz2 where


open import Cubical.Foundations.Prelude hiding (sym; funExt)
open import Leibniz.Base
open import Leibniz.Properties
open import Extra.Category.WellFounded
open import Extra.Category.Poly
open import Extra.Category
open import Extra.Algebra
open import Extra.ProgOrn.Desc
import Cubical.Data.Nat as N
open import Cubical.Data.Bool
open import Cubical.Data.Vec

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Prelude

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Glue public
  using (Glue ; glue ; unglue)

open import Cubical.Reflection.StrictEquiv

open import Cubical.Data.Equality                   as Eq  using () renaming (eqToPath to path)
open import Function.Base using (_∘′_)


NatD : Desc′
NatD = σ Bool λ
  { false → ṿ 0
  ; true  → ṿ 1 }

Nat : Set₁
Nat = μ NatD

open Algebra

-- this all seems like a lot more work than in Leibniz.Properties, but perhaps this is more mechanical/automatable somehow?

-- manual
bsuc₁ : Base Leibniz NatD → Leibniz
bsuc₁ (in-σ (false , in-ṿ []))      = 0b
bsuc₁ (in-σ (true  , in-ṿ (n ∷ []))) = bsuc n

L-Alg : Algebra (Ḟ NatD)
L-Alg .Carrier = Leibniz
L-Alg .forget  = bsuc₁

-- mechanical
data Peano-View : Leibniz → Type where
  as-zero : Peano-View 0b
  as-suc  : (n : Leibniz) (v : Peano-View n) → Peano-View (bsuc n)

view-1b : ∀ {n} → Peano-View n → Peano-View (n 1b)
view-2b : ∀ {n} → Peano-View n → Peano-View (n 2b)

view-1b as-zero      = as-suc 0b as-zero
view-1b (as-suc n v) = as-suc _ (view-2b v)

view-2b as-zero      = as-suc (0b 1b) (as-suc 0b as-zero)
view-2b (as-suc n v) = as-suc _ (as-suc _ (view-2b v))


view : (n : Leibniz) → Peano-View n
view 0b     = as-zero
view (n 1b) = view-1b (view n) 
view (n 2b) = view-2b (view n)

-- ?
view→Acc : ∀ {n} → Peano-View n → Acc NatD bsuc₁ n
view→Acc as-zero      = acc (in-σ (false , in-ṿ []) , refl) (acc-σ (acc-ṿ []))
view→Acc (as-suc n v) = acc (in-σ (true , in-ṿ (n ∷ [])) , refl) (acc-σ (acc-ṿ (view→Acc v ∷ [])))

Wf-bsuc : Wf NatD bsuc₁
Wf-bsuc n = view→Acc (view n)

-- mechanical ish
inj-bsuc : ∀ x y → _≡_ (bsuc₁ x) (bsuc₁ y) → _≡_ x y
inj-bsuc (in-σ (false , in-ṿ [])) (in-σ (false , in-ṿ []))           _ = refl
inj-bsuc (in-σ (false , in-ṿ [])) (in-σ (true , in-ṿ (x ∷ [])))      p = ⊥-rec (0b-not-bsuc x p)
inj-bsuc (in-σ (true , in-ṿ (x ∷ []))) (in-σ (false , in-ṿ []))      p = ⊥-rec (0b-not-bsuc x (sym p))
inj-bsuc (in-σ (true , in-ṿ (x ∷ []))) (in-σ (true , in-ṿ (y ∷ []))) p = congS (λ h → in-σ (true , in-ṿ (h ∷ []))) (Eq.eqToPath (bsuc-inj x y (Eq.pathToEq p)))

≡-lower : (ℓ : Level) {A : Type ℓ} {x y : A} → _≡_ {ℓ-max ℓ ℓ′} x y → _≡_ {ℓ} x y
≡-lower ℓ p i = p i

thm : _≃_ {ℓ-suc ℓ-zero} Leibniz (μ NatD)
thm = Wf+inj≃μ NatD L-Alg Wf-bsuc λ x y p → inj-bsuc x y (≡-lower ℓ-zero p)
\end{code}
