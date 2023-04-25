module Trees.Simple where

open import Prelude.UseAs
open import Prelude hiding (⟨_⟩)

data Digit : Set where
  1b 2b : Digit

data Number : Set where
  0n 1n : Number
  _⟨_⟩_ : Digit → Number → Digit → Number 

-- generic enumeration => define an obvious epi ℕ → Number
-- Q: why does this not help?

-- Q: can we control an associated index type for Number?
-- Q: is this obvious in any way?
data IxD : Digit → Set where
  1i      : IxD 1b
  2i1 2i2 : IxD 2b

data Ix : Number → Set where
  1i  :                     Ix 1n
  li  : ∀ {x y n} → IxD x → Ix (x ⟨ n ⟩ y)
  ri  : ∀ {x y n} → IxD y → Ix (x ⟨ n ⟩ y)
  mi  : ∀ {x y n} → Ix  n → Ix (x ⟨ n ⟩ y)
-- R: this is slightly more than Claessen's Try 1

{-
data Ix : Number → Set where
  1i  :                     Ix 1n
  li  : ∀ {x y n} → IxD x → Ix (x ⟨ n ⟩ y)
  ri  : ∀ {x y n} → IxD y → Ix (x ⟨ n ⟩ y)
  m1  : ∀ {x y n} → Ix  n → Ix (x ⟨ n ⟩ y)
  m2  : ∀ {x y n} → Ix  n → Ix (x ⟨ n ⟩ y)
-- R: this is exactly Claessen's Try 3
-- R: to give this amortized constant cons/snoc head/last we just have to add 3b : Digit
-}

-- R: we cannot fit Claessen's Try 4 into this, because of Tuple a = Pair a a | Triple a a a

-- R: this kind of finger tree can thus achieve at best
{-
     | amortized
-----+------
cons | 1
snoc | 1
++   | n
len  | 1?
!!   | log n
-}

-- R: also http://www.math.tau.ac.il/~haimk/adv-ds-2000/jacm-final.pdf
-- Q: catenable steques look like a numerical representation?

-- Q: I cannot read the definition of catenable deques in one go, so they may or may not be numerical representations
-- => actually I'm pretty sure they are not (non-trivially) because the recursive deques can be singles or doubles

-- Q: maybe it's interesting to find out where these differ from finger trees, or maybe that's a bit too purely functional for me

RepD : Set → Digit → Set
RepD A d = IxD d → A

Finger′ : ∀ A d → Def (RepD A d)
Finger′ A 1b = 
  (IxD 1b → A) ≡⟨ {!!} ⟩
  (⊤ → A)      ≡⟨ {!!} ⟩
  A            ∎ use-as-def
Finger′ A 2b = 
  (IxD 2b → A) ≡⟨ {!!} ⟩
  (⊤ ⊎ ⊤ → A)  ≡⟨ {!!} ⟩
  A × A        ∎ use-as-def

Finger : Set → Digit → Set
Finger A d = defined-by (Finger′ A d)

Rep : Set → Number → Set
Rep A n = Ix n → A

ix-0n : Ix 0n ≡ ⊥
ix-0n = ua (uninhabEquiv (λ ()) (λ ()))

ix-1n : Ix 1n ≡ ⊤
ix-1n = isContr→≡Unit (1i , (λ { 1i → refl }))

postulate
  ix-m : ∀ {x y n} → Ix (x ⟨ n ⟩ y) ≡ IxD x ⊎ (Ix n ⊎ IxD y)

Tree′ : ∀ A n → Def (Rep A n)
Tree : Set → Number → Set
Tree A n = defined-by (Tree′ A n)

Tree′ A 0n =
  (Ix 0n → A) ≡⟨ cong (λ x → (x → A)) ix-0n ⟩
  (⊥ → A)     ≡⟨ isContr→≡Unit isContr⊥→A  ⟩
  ⊤           ∎ use-as-def
Tree′ A 1n =
  (Ix 1n → A) ≡⟨ cong (λ x → (x → A)) ix-1n ⟩
  (⊤ → A)     ≡⟨ UnitToTypePath A ⟩
  A           ∎ use-as-def
Tree′ A (x ⟨ n ⟩ y) = 
  (Ix (x ⟨ n ⟩ y) → A) ≡⟨ cong (λ x → (x → A)) ix-m ⟩
  (IxD x ⊎ (Ix n ⊎ IxD y) → A) ≡⟨ ua Π⊎≃ ⟩
  {!!} ≡⟨ cong (λ x → x × _) (by-definition (Finger′ A x)) ⟩
  {!!} ≡⟨ cong (λ x → _ × x) (ua Π⊎≃) ⟩
  {!!} ≡⟨ cong (λ x → _ × (x × _)) (by-definition (Tree′ A n)) ⟩
  {!!} ≡⟨ cong (λ x → _ × (_ × x)) (by-definition (Finger′ A y)) ⟩
  Finger A x × Tree A n × Finger A y ∎ use-as-def


-- Conclusion: be more honest about your index types?
-- Numerical representations for catenable things are just going to be horrible
-- Maybe that's ok
