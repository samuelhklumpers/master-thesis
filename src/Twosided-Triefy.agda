{-# OPTIONS --cubical #-}

module Twosided-Triefy where

open import Cubical.Data.Nat
open import Cubical.Data.List as L
open import Cubical.Data.Vec
open import Cubical.Data.Maybe
open import ProgOrn.Ornaments hiding (_⋈_)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Prelude hiding (⌊_⌋; _◁_; _▷_)
open import Function.Base using (_$_)

{-
We know that there are as many implementations of flexible two-sided arrays as there are operations on them, each has their advantages and their drawbacks.
To name a few, we have:
- functions: trivial proofs; performance depends on construction, some extracting operations are linear (lookup, last)
- vectors: easy proof of iso to functions, performance does not depend on construction; some insertion operations are linear (insert, snoc, concat)
- braun trees: most operations are logarithmic (lookup, last, insert, snoc, concat); harder iso, cons and head are logarithmic
- random access: cons and head are constant; no snoc and last (or linear)

(I should make this into a table)

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

(it only occurs to me now that Ix seems to be a (weak) ring morphism?)
-}

data Three : Type where
  one two three : Three

DigitIx : Digit → Type
DigitIx d1 = ⊤
DigitIx d2 = Bool
DigitIx d3 = Three

data Index : DBin → Type where
  i1  : Index (con (t1 , _))
  il  : ∀ (l : Digit) {r x}   → DigitIx l → Index (con (tr , l , r , x , _))
  ir  : ∀ {l} (r : Digit) {x} → DigitIx r → Index (con (tr , l , r , x , _))
  itr : ∀ {l r x} → Index x → Bool → Index (con (tr , l , r , x , _))



data Index′ : DBin → Type where
  i0  : ∀ {d} → Index′ d
  i1  : Index′ (con (t1 , _))
  il  : ∀ (l : Digit) {r x}   → DigitIx l → Index′ (con (tr , l , r , x , _))
  ir  : ∀ {l} (r : Digit) {x} → DigitIx r → Index′ (con (tr , l , r , x , _))
  itr : ∀ {l r x} → Index′ x → Bool → Index′ (con (tr , l , r , x , _))

-- I bet you could "calculate" these if someone told you how toℕ acts on the constructors of DBin

{-
trieify A 0 = ⊤
trieify A 1 = A

trieify A (x < y > z) =
  Index (x < y > z) -> A
  DigitIx x + 2 × Index y + DigitIx z -> A
  Tup x A × (2 × Index y → A) × Tup z A
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

--Let's make sure it's still roughly List!

flatten : ∀ n → power n Two A → List A
flatten zero xs = [ xs ]
flatten (suc n) (xs , ys) = flatten n xs L.++ flatten n ys

DtoList : ∀ n {d} → Tup (power n Two A) d → List A
DtoList n (one a) = flatten n a
DtoList n (two a b) = flatten n a L.++ flatten n b
DtoList n (three a b c) = flatten n a L.++ flatten n b L.++ flatten n c

toList : Tree′ A n → List A
toList none                   = []
toList {n = n} (single x)     = flatten n x
toList {n = n} (deep pf m sf) = DtoList n pf L.++ toList m L.++ DtoList n sf

toList-cons′ : (x : El A n) (xs : Tree′ A n) → toList (cons′ x xs) ≡ flatten n x L.++ toList xs
toList-cons′ x none           = sym (++-unit-r _) 
toList-cons′ x (single y)     = refl
toList-cons′ {n = n} x (deep (one a) m sf) = L.++-assoc (flatten n x) (flatten n a) (toList m L.++ DtoList n sf)
toList-cons′ {n = n} x (deep (two a b) m sf) = L.++-assoc (flatten n x) _ _
toList-cons′ {n = n} x (deep (three a b c) m sf) = 
  (flatten n x L.++ flatten n a) L.++ toList (cons′ (b , c) m) L.++ DtoList n sf ≡⟨ cong (λ h → (flatten n x L.++ flatten n a) L.++ h L.++ DtoList n sf) (toList-cons′ (b , c) m) ⟩
  (flatten n x L.++ flatten n a) L.++ ((flatten n b L.++ flatten n c) L.++ toList m) L.++ DtoList n sf ≡⟨ L.++-assoc (flatten n x) _ _ ⟩
  flatten n x L.++ flatten n a L.++ ((flatten n b L.++ flatten n c) L.++ toList m) L.++ DtoList n sf ≡⟨ cong (λ h → flatten n x L.++ flatten n a L.++ h) (L.++-assoc (flatten n b L.++ flatten n c) _ _) ⟩
  flatten n x L.++ flatten n a L.++ (flatten n b L.++ flatten n c) L.++ toList m L.++ DtoList n sf ≡⟨ cong (flatten n x L.++_) (sym (L.++-assoc (flatten n a) _ _)) ⟩
  flatten n x L.++ (flatten n a L.++ flatten n b L.++ flatten n c) L.++ toList m L.++ DtoList n sf ∎



toTree : List A → Tree A
toTree []       = none
toTree (x ∷ xs) = cons′ x (toTree xs)

open import CrudeEquiv
open import Cubical.Functions.Surjection
open import Cubical.HITs.SetQuotients as SQ

toList-toTree : section (toList {A = A}) toTree
toList-toTree []       = refl
toList-toTree (x ∷ xs) = toList-cons′ _ (toTree xs) ∙ cong (x ∷_) (toList-toTree xs)

Tree↠List : Tree A ↠ List A
Tree↠List = toList , section→isSurjection {g = toTree} toList-toTree

TreeQ : Type → Type
TreeQ A = Tree A / λ x y → toList x ≡ toList y

TreeQ≃List : isSet A → TreeQ A ≃ List A
TreeQ≃List isSetA = crude (isOfHLevelList 0 isSetA) Tree↠List


open import Cubical.Foundations.SIP

Flex2S-Str : (A : Type) → Type → Type 
Flex2S-Str A X = (X → Maybe A) × (A → X → X) × (X → A → X)

Flex2S : Type → Type₁
Flex2S A = TypeWithStr ℓ-zero (Flex2S-Str A)

import Cubical.Structures.Auto as Auto

Flex2S-EquivStr : (A : Type) → (X Y : Flex2S A) → typ X ≃ typ Y → Type 
Flex2S-EquivStr A = Auto.AutoEquivStr (Flex2S-Str A)

Flex2S-UnivalentStr : (A : Type) → UnivalentStr _ (Flex2S-EquivStr A)
Flex2S-UnivalentStr A = Auto.autoUnivalentStr (Flex2S-Str A)

Flex2S-ΣPath : (A : Type) → (X Y : Flex2S A) → X ≃[ Flex2S-EquivStr A ] Y → X ≡ Y
Flex2S-ΣPath A = sip (Flex2S-UnivalentStr A)

headL : List A → Maybe A
headL []      = nothing
headL (x ∷ _) = just x

snocL : List A → A → List A
snocL []       y = L.[ y ]
snocL (x ∷ xs) y = x ∷ snocL xs y

headQ : TreeQ A → Maybe A
headQ = SQ.rec {!!} head′ {!!}

List-Flex2S : (A : Type) → Flex2S A
List-Flex2S A = List A , (headL , L._∷_ , snocL)

TreeQ-Flex2S : (A : Type) → isSet A → Flex2S A
TreeQ-Flex2S A isSetA = TreeQ A , ({!!} , {!!} , {!!})

TreeQ-Flex2S-List : (A : Type) (isSetA : isSet A) → TreeQ-Flex2S A isSetA ≡ List-Flex2S A
TreeQ-Flex2S-List A isSetA = Flex2S-ΣPath A _ _ {!!}

{-
TreeR : ∀ {A n} → Tree′ A n → Tree′ A n → Type
TreeR xs ys = toList xs ≡ toList ys

open import Cubical.HITs.SetQuotients as SQ

TreeQ : Type → ℕ → Type
TreeQ A n = Tree′ A n / TreeR

{-
inQ : ∀ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') → A → A / R
inQ R x = _/_.[ x ]

TreeREff : {A : Type} (a b : Tree′ A n) → inQ TreeR a ≡ inQ TreeR b → TreeR a b
TreeREff a b r = effective {!!} {!!} a b r -}

Tree≃List : isSet A → TreeQ A 0 ≃ List A
Tree≃List {A = A} isSetA = toList′ , record { equiv-proof = isEquivToList }
  where
  toList′ = SQ.rec (isOfHLevelList 0 isSetA) toList (λ a b r → r)
  
  isEquivToList : (y : List A) → isContr (fiber toList′ y)
  isEquivToList []       = (_/_.[ none ] , refl) , λ
    { (y , q) → ΣPathP ({!!} , {!!}) }
  isEquivToList (x ∷ xs) = {!!}
-}

{-
data TreeHIT (A : Type) : ℕ → Type where
  tree   : Tree′ A n → TreeHIT A n
  crunch : (xs ys : Tree′ A n) → toList xs ≡ toList ys → tree xs ≡ tree ys
  squash : isSet (TreeHIT A n)

Tree≃List : isSet A → TreeHIT A 0 ≃ List A
Tree≃List {A = A} isSetA = toList′ , record { equiv-proof = equiv-proof' }
  where
  toList′ : TreeHIT A 0 → List A
  toList′ (tree x) = toList x
  toList′ (crunch xs ys p i) = p i
  toList′ (squash xs ys p q i j) = isOfHLevelList 0 isSetA _ _ (cong toList′ p) (cong toList′ q) i j

  equiv-proof' : (y : List A) → isContr (fiber toList′ y)
  equiv-proof' []       = (tree none , refl) , {!h!}
    where
    h : (y : fiber toList′ []) → (tree (con (t0 , _)) , refl) ≡ y
    h (tree x , q) i = crunch none x (sym q) i , λ j → q (~ i ∨ j)
    h (crunch xs ys p i , q) j = {!isSet→SquareP (λ _ _ → isSetΣ squash λ x → isProp→isSet (isOfHLevelList 0 isSetA (toList′ x) [])) ? ? (λ _ → tree none , refl) ? i0 j!}
    h (squash xs ys p q i j , r) k = {!ΣPathP ({!!} , {!!})!}

  equiv-proof' (x ∷ xs) = {!!}
-}

-- ΣPathP (crunch _ x (sym q) , isSet→SquareP (λ _ _ → isOfHLevelList 0 isSetA) refl q (sym q) refl)
{-
Tree≃List : isSet A → TreeHIT A 0 ≃ List A
Tree≃List {A = A} isSetA = isoToEquiv (iso toList′ toTree′ sec ret)
  where
  toList′ : TreeHIT A 0 → List A
  toList′ (tree x) = toList x
  toList′ (crunch xs ys p i) = p i
  toList′ (squash xs ys p q i j) = isOfHLevelList 0 isSetA _ _ (cong toList′ p) (cong toList′ q) i j

  toTree′ : List A → TreeHIT A 0
  toTree′ xs = tree (toTree xs)

  sec : section toList′ toTree′
  sec []       = refl
  sec (x ∷ xs) = toList-cons′ _ (toTree xs) ∙ cong (x ∷_) (sec xs)

  isGroupoid→isPropSquare : ∀ {A : Type} → isGroupoid A → 
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → isProp (Square a₀₋ a₁₋ a₋₀ a₋₁)
  isGroupoid→isPropSquare Agpd a₀₋ a₁₋ a₋₀ a₋₁ = isOfHLevelRetractFromIso 1 (PathPIsoPath (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋) (Agpd _ _ _ _)

  ret : retract toList′ toTree′
  ret (tree x) = crunch _ _ (sec (toList x))
  ret (crunch xs ys p i) j = isSet→SquareP (λ _ _ → squash) (λ i → toTree′ (p i)) (crunch xs ys p) (ret (tree xs)) (ret (tree ys)) j i
  ret (squash xs ys p q i j) k = {!ugh!}
-}


-- the following is pretty disgusting, could we change something we did earlier to make this less chaotic?
-- > for starters you could give up and use ℕ, accepting that the slow _-_ gets compiled away, and the proof of correctness becomes... different
{-

-- now that the numbers are redundant, you can already tell this is going to get hairy
-- let's mirror FingerTree a bit


--type_case_of_ : (A : Type) → A → (A → B) → B
--type A case x of f = f x

-- compare digits, if d > e, then return the digit corresponding to d - e, otherwise return e - d + 1
_-d_ : (d e : Digit) → Digit ⊎ Digit
d1 -d d1 = inr d1
d1 -d d2 = inr d2
d1 -d d3 = inr d3
d2 -d d1 = inl d1
d2 -d d2 = inr d1
d2 -d d3 = inr d2
d3 -d d1 = inl d2
d3 -d d2 = inl d1
d3 -d d3 = inr d1

-- compare a number n and a digit d, if n < d, then return the corresponding index into d, otherwise return n - d 
digitComp : DBin → (d : Digit) → DigitIx d ⊎ DBin
digitComp (con (t0 , _)) d1 = inl tt
digitComp (con (t0 , _)) d2 = inl false
digitComp (con (t0 , _)) d3 = inl one
digitComp (con (t1 , _)) d1 = inr (con (t0 , _))
digitComp (con (t1 , _)) d2 = inl true
digitComp (con (t1 , _)) d3 = inl two
digitComp (con (tr , l , r , n , _)) d = case l -d d of λ {
  (inl l') → inr $ con (tr , l' , r , n , _) ; -- if l > d, then make a new number replacing l with l - d
  (inr d') → case digitComp n d' of λ { -- if d > l, then replace l with d1 and try to subtract n - (d - l + 1)
    (inl x) → {!!} ;
    (inr x) → inr $ con (tr , d1 , r , x , _) } } -- if n > d', replace n with n - d'

lookup′ : Tree′ A n → DBin → Maybe (El A n)
lookup′ (con (t0 , _)) ix = nothing
lookup′ (con (t1 , x , _)) ix = type DigitIx d1 ⊎ DBin case digitComp ix d1 of λ
  { (inl _)  → just x
  ; (inr _) → nothing } -- mildly hacky
lookup′ (con (tr , l , r , lx , rx , ts , _)) ix = {!!}
-}
