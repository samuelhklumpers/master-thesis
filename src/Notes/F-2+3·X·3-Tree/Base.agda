{-# OPTIONS --cubical #-}

module F-2+3·X·3-Tree.Base where

open import Cubical.Data.Nat
open import Cubical.Data.List as L
open import Cubical.Data.Maybe
open import Ext.ProgOrn.Ornaments hiding (_⋈_)
open import Prelude hiding (⌊_⌋; _◁_; _▷_)

{-
We know that there are as many implementations of flexible two-sided arrays as there are operations on them, each has their advantages and their drawbacks.

To recover the snoc and last for random access lists while keeping cons and head linear, and lookup logarithmic, we will move to a different datatype similar to "finger trees".
Remark, that finger trees are _not_ a numerical representation! The choice of Node in the Deep constructor obstructs re-interpretation of this constructor as multiplication by a constant.

Instead, we start from an inspired numeral system; from random access lists, we know that the operation corresponding to suc can be made constant time on the numerical representation.
By starting from a numeral system which has both a suc and cus, we can made cons and snoc both constant time, but we will also see that this loses the efficient append of finger trees.

Numbers in such a system would look like 1 < 2 < 0 > 1 > 2 to represent 1 + 2 * (2 + 2 * 0 + 1) + 2
Enumerating this type with suc produces a sequence like
0
1
1 < 0 > 1
2 < 0 > 1
1 < 1 > 1
2 < 1 > 1
1 < 1 < 0 > 1 > 1
2 < 1 < 0 > 1 > 1
1 < 2 < 0 > 1 > 1 
...
-}

data Digit : Type where
  d1 d2 d3 : Digit

data DBinTag : Type where
  t0 t1 tr : DBinTag

DBinD : Desc ⊤
DBinD tt = σ DBinTag λ
  { t0 → ṿ []
  ; t1 → ṿ []
  ; tr → Digit σ′ Digit σ′ ṿ [ tt ] }

DBin = μ DBinD tt

Dtoℕ : Digit → ℕ
Dtoℕ d1 = 1
Dtoℕ d2 = 2
Dtoℕ d3 = 2

toℕ : DBin → ℕ
toℕ (con (t0 , _)) = 0
toℕ (con (t1 , _)) = 1
toℕ (con (tr , l , r , n , _)) = Dtoℕ l + 2 · toℕ n + Dtoℕ r

{- let's derive DIndex: (note that indices of the same size can now get different shapes!)
IxD d = Fin (Dtoℕ d)

Ix 0 = 0
Ix 1 = 1
Ix (x < y > z) = IxD x + 2 × Ix y + IxD z -- using Ix (x + y) = Ix x + Ix y and Ix (x · y) = Ix x × Ix y

(it only occurs to me now that Ix seems to be a (weak) ring morphism?) -}

data Three : Type where
  one two three : Three

DigitIx : Digit → Type
DigitIx d1 = ⊤
DigitIx d2 = Bool
DigitIx d3 = Three

data LT : DBin → Type where
  i1  : LT (con (t1 , _))
  il  : ∀ (l : Digit) {r x}   → DigitIx l → LT (con (tr , l , r , x , _))
  ir  : ∀ {l} (r : Digit) {x} → DigitIx r → LT (con (tr , l , r , x , _))
  itr : ∀ {l r x} → LT x → Bool → LT (con (tr , l , r , x , _))

data LEQ : DBin → Type where
  i0  : ∀ {d} → LEQ d
  i1  : LEQ (con (t1 , _))
  il  : ∀ (l : Digit) {r x}   → DigitIx l → LEQ (con (tr , l , r , x , _))
  ir  : ∀ {l} (r : Digit) {x} → DigitIx r → LEQ (con (tr , l , r , x , _))
  itr : ∀ {l r x} → LEQ x → Bool → LEQ (con (tr , l , r , x , _))

-- I bet you could "calculate" these if someone told you how toℕ acts on the constructors of DBin

{-
trieify A 0 = ⊤
trieify A 1 = A

trieify A (x < y > z) =
  LT (x < y > z) -> A
  DigitIx x + 2 × LT y + DigitIx z -> A
  Tup x A × (2 × LT y → A) × Tup z A
  Tup x A × trieify (A × A) y × Tup z A
-}


data Tup (A : Type) : Digit → Type where
  one   : (a : A) → Tup A d1
  two   : (a b : A) → Tup A d2
  three : (a b c : A) → Tup A d3

Two : Type → Type
Two A = A × A

power : ℕ → (A → A) → A → A
power ℕ.zero    f = λ x → x
power (ℕ.suc n) f = f ∘ power n f

El : Type → ℕ → Type
El A d = power d Two A

TreeOD : Type → OrnDesc ℕ ! DBinD
TreeOD A (ok n) = σ DBinTag λ
  { t0 → ṿ _
  ; t1 → Δ[ _ ∈ El A n ] ṿ _ 
  ; tr → σ[ l ∈ Digit ] σ[ r ∈ Digit ] Δ[ _ ∈ Tup (El A n) l ] Δ[ _ ∈ Tup (El A n) r ] ṿ (ok (suc n) , _) }

-- can we compute some proofs if we define head/tail stuff on the desc instead of the type?

Tree′ : Type → ℕ → Type
Tree′ A = μ ⌊ TreeOD A ⌋

pattern none         = con (t0 , _)
pattern single x     = con (t1 , x , _)
pattern deep pf m sf = con (tr , _ , _ , pf , sf , m , _)

private variable
  n m : ℕ

TupHead : ∀ {A d} → Tup A d → A
TupHead (one x) = x
TupHead (two x _) = x
TupHead (three x _ _) = x

TupLast : ∀ {A d} → Tup A d → A
TupLast (one x) = x
TupLast (two _ x) = x
TupLast (three _ _ x) = x

head′ : Tree′ A n → Maybe (El A n)
head′ none           = nothing
head′ (single x)     = just x
head′ (deep pf m sf) = just (TupHead pf)

last′ : Tree′ A n → Maybe (El A n)
last′ none = nothing
last′ (single x) = just x
last′ (deep pf m sf) = just (TupLast sf)

cons′ : El A n → Tree′ A n → Tree′ A n
cons′ y none = single y
cons′ y (single x) = deep (one y) none (one x)
cons′ {A = A} {n = n} y (deep pf m sf) = more pf
  module Cons′ where
  more : ∀ {d} → Tup (El A n) d → Tree′ A n
  more (one a)       = deep (two y a) m sf
  more (two a b)     = deep (three y a b) m sf
  more (three a b c) = deep (two y a) (cons′ (b , c) m) sf

snoc′ : Tree′ A n → El A n → Tree′ A n
snoc′ none y = single y
snoc′ (single x) y = deep (one x) none (one y)
snoc′ {A = A} {n = n} (deep pf m sf) y = more sf
  where
  more : ∀ {d} → Tup (El A n) d → Tree′ A n
  more (one a) = deep pf m (two a y)
  more (two a b) = deep pf m (three a b y)
  more (three a b c) = deep pf (snoc′ m (a , b)) (two c y)

{-
crash′ : ∀ {i j k l} → Tup (El A n) i → Tree′ A (suc n) → Tup (El A n) j → Tup (El A n) k → Tree′ A (suc n) → Tup (El A n) l → Tree′ A n
-- clearly this is going nowhere unless j + k is even
-- we see that since we cannot extract or insert uneven numbers of elements from or into the trees
-- hence we cannot move around the elements of xr and yr without completely reconstructing xs or ys, thus crash′, and concat′ are necessarily linear in the worst case
crash′ xl xs xr yl ys yr = {!cons′ (TupHead xl) xs !}

concat′ : Tree′ A n → Tree′ A n → Tree′ A n
concat′ none ys = ys
concat′ (single x) ys = cons′ x ys
concat′ x@(deep pf m sf) none = x
concat′ x@(deep pf m sf) (single y) = snoc′ x y
concat′ (deep pf m sf) (deep pf′ m′ sf′) = {!!}
-}

size′ : Tree′ A n → DBin
size′ = ornForget ⌈ TreeOD _ ⌉

-- check! fold (λ x xs → 1 + xs) 0 xs = toℕ (size′ xs)

Tree : Type → Type
Tree A = Tree′ A 0
