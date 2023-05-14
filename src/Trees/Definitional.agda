{-# OPTIONS --with-K #-}

module Trees.Definitional where

open import Relation.Binary.PropositionalEquality

private variable
  A : Set

data Digit : Set where
  1b 2b : Digit

data Number : Set where
  0n 1n : Number
  _⟨_⟩_ : Digit → Number → Digit → Number 

data IxD : Digit → Set where
  1i      : IxD 1b
  2i1 2i2 : IxD 2b

data Ix : Number → Set where
  1i  :                     Ix 1n
  li  : ∀ {x y n} → IxD x → Ix (x ⟨ n ⟩ y)
  ri  : ∀ {x y n} → IxD y → Ix (x ⟨ n ⟩ y)
  mi  : ∀ {x y n} → Ix  n → Ix (x ⟨ n ⟩ y)
  
RepD : Set → Digit → Set
RepD A d = IxD d → A

Rep : Set → Number → Set
Rep A n = Ix n → A


-- also note that the representability of any sufficiently complicated number type is a bit useless, as illustrated by
suc : Number → Number
suc 0n = 1n
suc 1n = 1b ⟨ 0n ⟩ 1b
suc (1b ⟨ m ⟩ r) = 2b ⟨ m ⟩ r
suc (2b ⟨ m ⟩ r) = 2b ⟨ suc m ⟩ r

izero : ∀ {n} → Ix (suc n)
izero {n = 0n} = 1i
izero {n = 1n} = li 1i
izero {n = 1b ⟨ m ⟩ r} = li 2i1
izero {n = 2b ⟨ m ⟩ r} = li 2i1

isucc : ∀ {n} → Ix n → Ix (suc n)
isucc {n = .1n} 1i = ri 1i
isucc {n = .(1b ⟨ _ ⟩ _)} (li 1i) = li 2i2
isucc {n = .(2b ⟨ _ ⟩ _)} (li 2i1) = li 2i2
isucc {n = .(2b ⟨ _ ⟩ _)} (li 2i2) = mi izero
isucc {n = 1b ⟨ _ ⟩ _} (ri x) = ri x
isucc {n = 1b ⟨ _ ⟩ _} (mi i) = mi i
isucc {n = 2b ⟨ _ ⟩ _} (ri x) = ri x
isucc {n = 2b ⟨ _ ⟩ _} (mi i) = mi (isucc i)

head : ∀ n → Rep A (suc n) → A
head n xs = xs izero

-- you cannot take the head of a concrete represented tree without specifying its size
{-
Tree-2 : Rep Number (1b ⟨ 1n ⟩ 2b)
Tree-2 (li 1i) = 1n
Tree-2 (ri x) = 0n
Tree-2 (mi ix) = 0n


try-1 : head _ (Tree-2) ≡ 1n
try-1 = {!!}
-}
-- that's a bit useless, but you can still write something that calculates this I suppose

data IxV : ∀ n → Ix (suc n) → Set where
  as-izero : ∀ {n} → IxV n izero
  as-isucc : ∀ {n} → (i : Ix n) → IxV n (isucc i)
  

iview : ∀ n → (i : Ix (suc n)) → IxV n i
iview 0n 1i = as-izero
iview 1n (li 1i) = as-izero
iview 1n (ri 1i) = as-isucc 1i
iview (1b ⟨ m ⟩ r) (li 2i1) = as-izero
iview (1b ⟨ m ⟩ r) (li 2i2) = as-isucc (li 1i)
iview (1b ⟨ m ⟩ r) (ri x) = as-isucc (ri x)
iview (1b ⟨ m ⟩ r) (mi i) = as-isucc (mi i)
iview (2b ⟨ m ⟩ r) (li 2i1) = as-izero
iview (2b ⟨ m ⟩ r) (li 2i2) = as-isucc (li 2i1)
iview (2b ⟨ m ⟩ r) (ri x) = as-isucc (ri x)
iview (2b ⟨ m ⟩ r) (mi i) with iview _ i
... | as-izero   = as-isucc (li 2i2)
... | as-isucc i = as-isucc (mi i)

cons : ∀ n → A → Rep A n → Rep A (suc n)
cons n x xs i with iview n i
... | as-izero   = x
... | as-isucc i = xs i

-- could you split on Index-View izero in Calculating Datastructures?

iview-z : ∀ n → iview n izero ≡ as-izero
iview-z 0n = refl
iview-z 1n = refl
iview-z (1b ⟨ n ⟩ x₁) = refl
iview-z (2b ⟨ n ⟩ x₁) = refl

-- at least this "works" (note that this involves splitting on xs for the concrete type)
head-cons : ∀ n x (xs : Rep A n) → head _ (cons _ x xs) ≡ x
head-cons n x xs with iview n izero | iview-z n
... | .as-izero | refl = refl
