module FunOrn.Example where

open import Function
open import Relation.Binary.PropositionalEquality

-- Nat to List, and its reornament Vec

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

data List (A : Set) : Set where
  nil : List A
  cons : (a : A)(xs : List A) → List A

forgetList : ∀{A} → List A → ℕ
forgetList nil = zero
forgetList (cons a xs) = suc (forgetList xs)

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : ∀{n} → (a : A)(xs : Vec A n) → Vec A (suc n)

makeVec : ∀{A} → (xs : List A) → Vec A (forgetList xs)
makeVec nil = nil
makeVec (cons a xs) = cons a (makeVec xs)

-- Bool to Maybe, and its reornament IMaybe

data Bool : Set where
  true false : Bool

data Maybe (A : Set) : Set where
  just : (a : A) → Maybe A
  nothing : Maybe A

forgetMaybe : ∀{A} → Maybe A → Bool
forgetMaybe nothing = false
forgetMaybe (just a) = true

data IMaybe (A : Set) : Bool → Set where
  just : (a : A) → IMaybe A true
  nothing : IMaybe A false

forgetIMaybe : ∀{A b} → IMaybe A b → Maybe A
forgetIMaybe {b = false} nothing = nothing
forgetIMaybe {b = true} (just a) = just a

coh-IMaybe : ∀{A b} → (ma : IMaybe A b) → forgetMaybe (forgetIMaybe ma) ≡ b
coh-IMaybe nothing = refl
coh-IMaybe (just a) = refl

-- Less than

_<_ : ℕ → ℕ → Bool
m < zero = false
zero < suc n = true
suc m < suc n = m < n

-- Coq-style implementation and proof of lookup

lookup' : ∀{A} → ℕ → List A → Maybe A
lookup' n nil = nothing
lookup' zero (cons a xs) = just a
lookup' (suc n) (cons a xs) = lookup' n xs

coh-lookup' : ∀{A} → (m : ℕ)(xs : List A) →
             forgetMaybe (lookup' m xs) ≡ m < (forgetList xs)
coh-lookup' m nil = refl
coh-lookup' zero (cons a xs) = refl
coh-lookup' (suc m) (cons a xs) = coh-lookup' m xs

-- Correct-by-construction lookup

ilookup : ∀{A} → (m : ℕ) →
                 {n : ℕ} → Vec A n →
                 IMaybe A (m < n)
ilookup m nil = nothing
ilookup zero (cons a ys) = just a
ilookup (suc m) (cons a ys) = ilookup m ys

lookup : ∀{A} → ℕ → List A → Maybe A
lookup n xs = forgetIMaybe (ilookup n (makeVec xs))


coh-lookup :  ∀{A} → (m : ℕ)(xs : List A) →
             forgetMaybe (lookup m xs) ≡ m < (forgetList xs)
coh-lookup m = coh-IMaybe ∘ (ilookup m) ∘ makeVec