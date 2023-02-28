{-# OPTIONS --cubical --copatterns --postfix-projection --allow-unsolved-metas #-}

module Nary-List where

open import Prelude hiding (⌊_⌋)
open import ProgOrn.Ornaments

open import Data.List hiding (fromMaybe)
import Data.Vec as V

import Cubical.Data.Nat as N
import Data.Fin as Fin
open import Data.Bool
open import Data.Fin hiding (toℕ)
open import Data.Maybe

import Cubical.Data.Equality as Eq


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

power : ℕ → (A → A) → A → A
power ℕ.zero    f = λ x → x
power (ℕ.suc n) f = f ∘ power n f

-- An n-Tree (unindexed) at level d can either be
TreeOD : ∀ A n → OrnDesc ℕ ! (n -aryD)
TreeOD A n (ok d) = σ (Fin n) (λ
  { zero    → ṿ _
    -- empty
  ; (suc s) → Δ (V.Vec (power d (λ X → V.Vec X n) A) (Fin.toℕ (suc s))) λ _ → ṿ (ok (N.suc d) , _) })
    -- hold n^d * s elements and hold an n-Tree of level (suc d)

Tree : ∀ A n d → Type
Tree A n = μ ⌊ TreeOD A n ⌋

-- by now we might also observe that my approach has devolved into Josh Ko's but with a different starting point

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

-- we should be able to upgrade things now

-- why
-- Treeᵁ : ∀ A n → Upgrade ((m : n -ary) → Ix n m → n -ary) {!Tree A n → Tree n (suc s) A!}

n-ary-Tree : ∀ A n d → Promotion (n -ary) (Tree A n d)
n-ary-Tree A n = ornProm ⌈ (TreeOD A n) ⌉

open Promotion

IdP : ∀ A → Promotion A A
IdP A .Predicate  = λ A → ⊤
IdP A .forget     = λ x → x
IdP A .complement = !
IdP A .promote    = λ x _ → x
IdP A .coherence  = λ _ _ → Eq.refl

unMaybe : {A B : Type} → (f : A → B) → B → Maybe A → Maybe B
unMaybe f b (just x) = just (f x)
unMaybe f b nothing  = just b

decrement : ∀ n → n -ary → Maybe (n -ary)
decrement _ (con (zero  , _))           = nothing
decrement _ (con (suc zero    , s , _)) = unMaybe (λ t → con (fromℕ _ , t , _)) (con (zero , _)) (decrement _ s)
decrement _ (con (suc (suc i) , s , _)) = just (con (inject₁ (suc i) , s , _))

{-
-- maybe more complicated than the example merits

subtract : ∀ n → n -ary → n -ary → Maybe (n -ary)
subtract n x y = {!!}

Treeᵁ : ∀ A n → Upgrade (n -ary → n -ary → Maybe (n -ary)) (Tree A n → n -ary → Maybe (Tree A n))
Treeᵁ A n = n-ary-Tree A n ⇀ (IdP _ ⇀ toUpgrade (MaybeP (n-ary-Tree A n)))
-}

decrement-upg : ∀ A n → Upgrade (n -ary → Maybe (n -ary)) ({d : ℕ} → Tree A n d → Maybe (Tree A n d))
decrement-upg A n = ∀⁺[[ d ∈ ℕ ]] (n-ary-Tree A n d ⇀ toUpgrade (MaybeP (n-ary-Tree A n d)))

maybe' : {A B : Type} {X : A → Set} {Y : B → Set} {f : A → B} → ({a : A} → X a → Y (f a)) → {b : B} → Y b → {ma : Maybe A} → Maybe' X ma → Maybe' Y (unMaybe f b ma) 
maybe' f b (just x) = just (f x)
maybe' f b nothing  = just b

-- late to the party
pattern zeroᵁ     = con (zero  , _)
pattern prefᵁ i s = con (suc i , s , _)

pattern leafᵁ        = con _
pattern nodeᵁ xs xss = con (xs , xss , _)

tailᵁ : ∀ A n → Upgrade.Predicate (decrement-upg A n) (decrement n)
tailᵁ A n zeroᵁ             leafᵁ          = nothing
tailᵁ A n (prefᵁ zero s)    (nodeᵁ xs xss) = maybe' (λ t → nodeᵁ {!need to take some elements from xss and move them to xs!} t) leafᵁ (tailᵁ A n s xss)
tailᵁ A n (prefᵁ (suc i) s) (nodeᵁ xs xss) = just (nodeᵁ {!subst (V.Vec A) (cong ℕ.suc pf) (V.tail xs)!} xss)
  where
  pf : ∀ {n} {i : Fin n} → Fin.toℕ i ≡ Fin.toℕ (inject₁ i)
  pf {i = zero}  = refl
  pf {i = suc i} = cong ℕ.suc pf
