{-# OPTIONS --with-K #-}

module Trees.Honest where

--open import Prelude.UseAs
--open import Prelude hiding (⟨_⟩)

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- Q: What is a number system with an associated index type?

data Term   : Set
data Number : Set

data Term where
  [_]     : (c : ℕ)                         → Term
  _+1*_∷_ : (m : ℕ) (n : Number) (t : Term) → Term 

data Number where
  [] var :                        Number
  _∷_ : (t : Term) (n : Number) → Number

infixr 10 _∷_

⟦_⟧ₙ_ : Number → Set → Set
⟦_⟧ₜ_ : Term   → Set → Set

⟦ []    ⟧ₙ X = ⊥
⟦ var   ⟧ₙ X = X
⟦ t ∷ n ⟧ₙ X = (⟦ t ⟧ₜ X) ⊎ (⟦ n ⟧ₙ X)

⟦ [ _ ]       ⟧ₜ X = ⊤
⟦ _ +1* n ∷ t ⟧ₜ X = ⟦ n ⟧ₙ X × ⟦ t ⟧ₜ X

data μₙ (n : Number) : Set where
  con : ⟦ n ⟧ₙ μₙ n → μₙ n

Intpₙ : ∀ n → μₙ n → ℕ
Intpₙ n (con x) = goₙ n x
  where
  goₙ : ∀ m → ⟦ m ⟧ₙ μₙ n → ℕ
  goₜ : ∀ t → ⟦ t ⟧ₜ μₙ n → ℕ
  
  goₙ var      (con x) = goₙ n x
  goₙ (t ∷ m) (inj₁ x) = goₜ t x
  goₙ (t ∷ m) (inj₂ x) = goₙ m x

  goₜ [ c ]         tt      = c
  goₜ (m +1* n ∷ t) (x , y) = suc m * goₙ n x + goₜ t y

module Example where
  Nat′ : Number
  Nat′ = [ 0 ] ∷ (0 +1* var ∷ [ 1 ]) ∷ []

  Nat = μₙ Nat′

  Nat-2 : Nat
  Nat-2 = con (inj₂ (inj₁ ((con (inj₂ (inj₁ (con (inj₁ _) , _)))) , _)))

  2≡2 : Intpₙ Nat′ Nat-2 ≡ 2
  2≡2 = refl

  Bin′ : Number
  Bin′ = [ 0 ] ∷ (1 +1* var ∷ [ 1 ]) ∷ (1 +1* var ∷ [ 2 ]) ∷ []

  Bin = μₙ Bin′

  Bin-5 : Bin
  Bin-5 = con (inj₂ (inj₁ (con (inj₂ (inj₂ (inj₁ (con (inj₁ _) , _)))) , _)))

  5≡5 : Intpₙ Bin′ Bin-5 ≡ 5
  5≡5 = refl

Ixₙ : ∀ {n} → (μₙ n → Set) → (m : Number) → ⟦ m ⟧ₙ μₙ n → Set
Ixₜ : ∀ {n} → (μₙ n → Set) → (t : Term)   → ⟦ t ⟧ₜ μₙ n → Set

Ixₙ X []      _ = ⊥
Ixₙ X var     x = X x
Ixₙ X (t ∷ n) (inj₁ x) = Ixₜ X t x
Ixₙ X (t ∷ n) (inj₂ y) = Ixₙ X n y

Ixₜ X [ c ]         tt      = Fin c
Ixₜ X (m +1* n ∷ t) (x , y) = Fin (suc m) × Ixₙ X n x ⊎ Ixₜ X t y

data Ix : ∀ n → μₙ n → Set where
  ix : ∀ {n x} → Ixₙ (Ix n) n x → Ix n (con x)

-- R: something like this, I think, anyway

module Example-2 where
  open Example

  NatFin = Ix Nat′

  Fin-2 : NatFin Nat-2
  Fin-2 = ix (inj₁ (zero , ix (inj₂ zero)))
  
  {-
  Fin-2 : NatFin Nat-2
  Fin-2 = ix (inj₁ (zero , ix (inj₁ (zero , ix {!Fin 0!}))))
  -}

-- Q: can we now compute the associated datastructure Container n, and construct a proof that Container n x A ≡ Ix n x → A?
-- probably
