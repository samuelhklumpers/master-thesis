{-# OPTIONS --with-K #-}

module Trees.OriginalTrivial where


-- Q: can we give a trivial¹ numerical representation that fits onto the original finger trees

-- 1: by trivial, I mean something that looks like FingerTree ⊤

open import Trees.Honest
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- A: not without adding indices or making the numbers nested recursive types ha ha ha...
-- it's not like that obstructs interpreting them as numbers or deriving the indices though, does it?
-- (you just have to deal with two indices)


-- Q: alternatively, directly define Ix : FingerTree ⊤ → Set?

data Finger (A : Set) : Set where
  one   : A         → Finger A
  two   : A → A     → Finger A
  three : A → A → A → Finger A

data Node (A : Set) : Set where
  pair   : A → A     → Node A
  triple : A → A → A → Node A

data FingerTree (A : Set) : Set where
  none   : FingerTree A
  single : A → FingerTree A
  deep   : Finger A → FingerTree (Node A) → Finger A → FingerTree A

cons : ∀ {A} → A → FingerTree A → FingerTree A
cons x none = single x
cons x (single y) = deep (one x) none (one y)
cons x (deep (one x₁) m r) = deep (two x x₁) m r
cons x (deep (two x₁ x₂) m r) = deep (three x x₁ x₂) m r
cons x (deep (three x₁ x₂ x₃) m r) = deep (two x x₁) (cons (pair x₂ x₃) m) r

snoc : ∀ {A} → FingerTree A → A → FingerTree A
snoc none x = single x
snoc (single x₁) x = deep (one x₁) none (one x)
snoc (deep l xs (one x₂)) x = deep l xs (two x₂ x)
snoc (deep l xs (two x₂ x₃)) x = deep l xs (three x₂ x₃ x)
snoc (deep l xs (three x₂ x₃ x₄)) x = deep l (snoc xs (pair x₂ x₃)) (two x₄ x)


power : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → A → A
power zero    f x = x
power (suc n) f x = f (power n f x)



data IxN : ∀ n → power n Node ⊤ → Set where
  i0 : IxN 0 tt
  2l : ∀ {n} {x y : power n Node ⊤} → IxN n x → IxN (suc n) (pair x y)
  2r : ∀ {n} {x y : power n Node ⊤} → IxN n y → IxN (suc n) (pair x y)

  3l : ∀ {n} {x y z : power n Node ⊤} → IxN n x → IxN (suc n) (triple x y z)
  3m : ∀ {n} {x y z : power n Node ⊤} → IxN n y → IxN (suc n) (triple x y z)
  3r : ∀ {n} {x y z : power n Node ⊤} → IxN n z → IxN (suc n) (triple x y z)

data IxF : ∀ n → Finger (power n Node ⊤) → Set where
  1i0 : ∀ {n x} → IxN n x → IxF n (one x)

  2i0 : ∀ {n x y} → IxN n x → IxF n (two x y)
  2i1 : ∀ {n x y} → IxN n y → IxF n (two x y)

  3i0 : ∀ {n x y z} → IxN n x → IxF n (three x y z)
  3i1 : ∀ {n x y z} → IxN n y → IxF n (three x y z)
  3i2 : ∀ {n x y z} → IxN n z → IxF n (three x y z)

data IxFT : ∀ n → FingerTree (power n Node ⊤) → Set where
  s0 : ∀ {n x} → IxN n x → IxFT n (single x)

  dl : ∀ {n l m r} → IxF n l → IxFT n (deep l m r)
  dm : ∀ {n l m r} → IxFT (suc n) m → IxFT n (deep l m r)
  dr : ∀ {n l m r} → IxF n r → IxFT n (deep l m r)

FT : ∀ n → FingerTree (power n Node ⊤) → Set → Set
FT n xs A = IxFT n xs → A

shape : ∀ {A} n → power n Node A → power n Node ⊤
shape zero x = tt
shape (suc n) (pair x x₁) = pair (shape n x) (shape n x₁)
shape (suc n) (triple x x₁ x₂) = triple (shape n x) (shape n x₁) (shape n x₂)

cons′ : ∀ {A n} (ns : FingerTree (power n Node ⊤)) → (x : power n Node A) → FT n ns A → FT n (cons (shape n x) ns) A
cons′ ns x xs = {!!}
-- R: so it's completely pointless, because to get something from the representable fingertrees, you first must solve the same equality on the type level on the actual fingertrees 
