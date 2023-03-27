module FingerTree2 where

open import Cubical.Data.Nat
open import Cubical.Data.List
open import ProgOrn.Ornaments
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Prelude hiding (⌊_⌋; _◁_)


-- a second stab at fingertrees

{-
data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)

data Digit a = One a | Two a a | Three a a a | Four a a a a
data Node a = Node2 a a | Node3 a a a
-}

-- so we can start by putting FingerNumber ~ FingerTree ⊤

{-
data FingerNumber = Empty
                  | Single
                  | Deep (Digit ⊤) (FingerTree (Node ⊤)) (Digit ⊤)

data Digit a = One a | Two a a | Three a a a | Four a a a a
data Node a = Node2 a a | Node3 a a a
-}

-- failure!
-- we can relax FingerNumber n ~ FingerTree (pow n Node ⊤)
-- P n = pow n Node ⊤


{-
data FingerNumber n = Empty
                  | Single (P n)
                  | Deep (Digit (P n)) (FingerTree (Node (P n)) = FingerNumber (suc n)) (Digit (P n))

data Digit a = One a | Two a a | Three a a a | Four a a a a
data Node a = Node2 a a | Node3 a a a
-}

-- collapsing

{-
P n = pow n Node ⊤
so we might as well take
-}

private variable
  n : ℕ

data Node : ℕ → Type where
  node0 : Node 0
  node1 : Node n → Node n          → Node (suc n)
  node2 : Node n → Node n → Node n → Node (suc n)

data Digit (n : ℕ) : Type where
  one   : Node n → Digit n
  two   : Node n → Node n → Digit n
  three : Node n → Node n → Node n → Digit n
  four  : Node n → Node n → Node n → Node n → Digit n

data FingerNumber : ℕ → Type where
  none  : FingerNumber n
  one   : Node n → FingerNumber n
  deep  : Digit n → Digit n → FingerNumber (suc n) → FingerNumber n

{-
F→N : FingerNumber n → ℕ
F→N none         = 0
F→N (one n)      = {!!}
F→N (deep d e f) = {!!}
-}

-- but this is kind of useless because it's not like you'd use Tree ⊤ as a binary number...
-- we're (trying) to make something like perfect fingertrees instead...

-- but that's hard because fingertrees are designed to have some imbalance to allow some operations to be faster..

-- (i.e. the nodes are what's stopping us) (or are they??? i suppose even if you made the numeral system in the dumb way it would still have logarithmic +?)

-- but I suppose two-sided binary would have the same benefits with less chaos
