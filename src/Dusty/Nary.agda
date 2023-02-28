{-# OPTIONS --cubical #-}

module Nary where

open import Prelude hiding (⌊_⌋)
open import ProgOrn.Ornaments

open import Data.List
import Data.Vec as V

import Cubical.Data.Nat as N
import Data.Fin as Fin
open import Data.Bool
open import Data.Fin hiding (toℕ)

-- An n -ary number can either be 
_-aryD : ℕ → Desc ⊤
(n -aryD) tt = σ (Fin n) λ
  { zero     → ṿ []         -- zero
  ; (suc ix) → ṿ [ tt ] }   -- a digit following an n-ary number

_-ary : ℕ → Type
n -ary = μ (n -aryD) tt

toℕ : ∀ n → n -ary → ℕ
toℕ _ (con (zero  , _))       = 0
toℕ n (con (suc i , (x , _))) = (Fin.toℕ i) N.+ (n N.· toℕ n x)

-- An n -Tree can either be 
_-TreeOD : ∀ n → OrnDesc (n -ary × Type) ! (n -aryD)
(n -TreeOD) (ok (con (zero  , _)       , A)) = ∇ zero (ṿ _)
   -- of size zero and empty
(n -TreeOD) (ok (con (suc i , (s , _)) , A)) = ∇ (suc i) (Δ (V.Vec A (Fin.toℕ (suc i))) (λ _ → ṿ (ok (s , V.Vec A n) , _)))
   -- of size x, where x is (suc i) preceding s, and be a node with (suc i) elements and have a subtree of size s where the elements are Vectors of size n 
-- so like pretty heavy nesting

Tree : ∀ n s → (A : Type) → Type (ℓ-suc ℓ-zero) -- yeah that's unfortunate
Tree n s A = μ ⌊ n -TreeOD ⌋ (s , A)
-- i guess we could form a small universe again to describe functions on indices without inflating the levels of the resultant types

{- NZ : ∀ {n} → Fin n → Type
NZ zero    = ⊥
NZ (suc i) = ⊤ -}

-- The following idea of ornamenting numbers to indices is adapted from the source of McBride's Transporting Functions across Ornaments
-- An index into an n -Tree can either
IxOD : ∀ n → OrnDesc (n -ary) ! (n -aryD)
IxOD n (ok (con (zero  , m)))       = Δ ⊥ (λ ()) -- inaccessible
IxOD n (ok (con (suc i , (m , _)))) = σ (Fin n) λ
  { zero    → Δ (Fin′ (suc i)) (λ _ → ṿ _)
    -- index into this node 
  ; (suc j) → Δ (Fin n) (λ _ → ṿ (ok m , _)) }
    -- pick one of n branches, provided i is nonzero, and index deeper into this branch

Ix : ∀ n → n -ary → Type
Ix n = μ ⌊ IxOD n ⌋

-- now we can implement lookup without having to think too much
-- (but the time to write it is heavily dominated by the time spent getting past the encoding overhead....)
lookupT : ∀ n s {A} → Tree n s A → Ix n s → A
lookupT n (con (suc i , s))     (con (xs , _))      (con (zero  , k , _))      = V.lookup xs k
lookupT n (con (suc i , s , _)) (con (_ , xss , _)) (con (suc j , k , ks , _)) = V.lookup (lookupT n s xss ks) k

-- Okasaki says that for large s, n ∈ {3 , 4} can give better performance than n = 2,
-- although the actual performance of this would probably be monstrous given the amount of computation that goes on in the background

-- we should be able to upgrade things now

-- can we upgrade _-_ to lookup?
-- > what is _-_?
-- 1. n -ary → n -ary → Maybe (n -ary)
-- 2. (x : n -ary) → Ix n x → n -ary

-- 1. yeah
-- 2. upgrades may or may not topple over if we push them that far

-- let's play it safe and just upgrade suc for now
{-
Treeᵁ : ∀ A n → Upgrade (n -ary → n -ary) {!{s : n -ary} → A → Tree n s A → Tree n (suc s) A!}
Treeᵁ = {!OptP!}
-}

-- I think I see a problem now
