open import Level
  renaming ( zero to zeroL
           ; suc to sucL )

module Logic.IProp where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Data.Nat

--open import Category.Applicative
--open import Category.Applicative.Indexed

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

-- 1. We define a sub-universe of irrelevant proofs:

infixr 1 ⊢_
data ⊢_ {ℓ : Level} (X : Set ℓ) : Set ℓ where
  pf : .X → ⊢ X

{- BAD:
≡-relevant : {A : Set} {a b : A} → ⊢ a ≡ b → a ≡ b
≡-relevant a≡b = trustMe
-}

-- 2. We postulate extensionality in there:

postulate 
  extensionality : ∀{k ℓ}{A : Set k}{B : A → Set ℓ}{f g : (a : A) → B a} →
                   ((x : A) → ⊢ (f x ≡ g x)) → ⊢ (f ≡ g)

module Applicative {ℓ : Level} where

--   Applicative⊢ : RawApplicative ⊢_
--   Applicative⊢ = record { pure = pf
--                         ; _⊛_ = _⊛_ }
--       where _⊛_ : {A B : Set } → ⊢ (A → B) → ⊢ A → ⊢ B
--             (pf f) ⊛ (pf a) = pf (f a)

--   open RawIApplicative Applicative⊢ public

-- 3. ???

-- 4. We *have* proof irrelevance:

  pf-irrelevance : {A : Set }
                   (a : ⊢ A)(b : ⊢ A) → ⊢ (a ≡ b)
  pf-irrelevance (pf _) (pf _) = pf refl

-- 5. This encapsulated notion of equality is substitutive 
--    (it better has to)

  trans⊢ : {A : Set }{a b c : A} → ⊢ (a ≡ b) → ⊢ (b ≡ c) → ⊢ (a ≡ c)
  trans⊢ (pf x) (pf y) = pf (trans x y)

{-
trans⊢' : {A : Set}{a b c : A} → ⊢ (a ≡ b) → ⊢ (b ≡ c) → ⊢ (a ≡ c)
trans⊢' x y = pure trans ⊛ x ⊛ y
-}

  subst⊢ : {A B : Set }(P : A → Set ){x y : A} → ⊢ (x ≡ y) → ⊢ (P x) → ⊢ (P y)
  subst⊢ f (pf x≡y) (pf Px) = pf (subst f x≡y Px)

  cong⊢ : ∀ {A B : Set }
         (f : A → B) {x y} → ⊢ (x ≡ y) → ⊢ (f x ≡ f y)
  cong⊢ f (pf x≡y) = pf (cong f x≡y)


-- 6. We prove (\x → 0 + x) ≡ (\x → x + 0)

-- intensionally:
{-
0+x : (x : ℕ) → 0 + x ≡ x + 0
0+x 0 = refl
0+x (suc n) = cong suc (0+x n)

-- extensionally!
open Data.Nat

ext-0+x : ⊢ ((\x → 0 + x) ≡ (\x → x + 0))
ext-0+x = extensionality (\n → pf (0+x n))
-}
-- 7. This is not OTT, just poor man's proof irrelevance:

--open import Data.Bool

{- NO WAY!
⊥*-elim : {X : Set} → ⊢ ⊥ → X
⊥*-elim {X} (pf b) with ≡-relevant (pf (⊥-elim {Whatever = true ≡ false} b))
⊥*-elim (pf b) | ()
-}

-- 'variable b is declared irrelevant, so it cannot be used here
--    when checking that the expression b has type ⊥'
