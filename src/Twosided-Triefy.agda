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

-- I probably should have used this as the implementation
snocL-++ : (xs : List A) (x : A) → xs L.++ L.[ x ] ≡ snocL xs x
snocL-++ [] x = refl
snocL-++ (y ∷ xs) x = cong (y ∷_) (snocL-++ xs x)

head-toList : (a : Tree A) → headL (toList a) ≡ head′ a
head-toList none = refl
head-toList (single x) = refl
head-toList (deep (one a) m sf) = refl
head-toList (deep (two a b) m sf) = refl
head-toList (deep (three a b c) m sf) = refl

List-Flex2S : (A : Type) → Flex2S A
List-Flex2S A = List A , (headL , L._∷_ , snocL)


toList-snoc′ : (xs : Tree′ A n) (x : El A n) → toList (snoc′ xs x) ≡ toList xs L.++ flatten n x
toList-snoc′ none x = refl
toList-snoc′ (single y) x = refl
toList-snoc′ {n = n} (deep pf m (one a)) x = sym (L.++-assoc (DtoList n pf) _ _ ∙ (cong (DtoList n pf L.++_) (L.++-assoc (toList m) (flatten n a) _)))
toList-snoc′ {n = n} (deep pf m (two a b)) x = sym (L.++-assoc (DtoList n pf) _ _ ∙ cong (DtoList n pf L.++_) (L.++-assoc (toList m) _ _ ∙ cong (toList m L.++_) (L.++-assoc (flatten n a) _ _)))
toList-snoc′ {n = n} (deep pf m (three a b c)) x = 
  DtoList n pf L.++ toList (snoc′ m (a , b)) L.++ flatten n c L.++ flatten n x
    ≡⟨ cong (λ h → DtoList n pf L.++ h L.++ flatten n c L.++ flatten n x) (toList-snoc′ m (a , b)) ⟩
  DtoList n pf L.++ (toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c L.++ flatten n x ≡⟨ sym (L.++-assoc (DtoList n pf) _ _) ⟩
  (DtoList n pf L.++ (toList m L.++ flatten n a L.++ flatten n b)) L.++ flatten n c L.++ flatten n x ≡⟨ sym (L.++-assoc (DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b) (flatten n c) (flatten n x)) ⟩
  ((DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c) L.++ flatten n x ≡⟨ cong (L._++ flatten n x) (L.++-assoc (DtoList n pf) _ _) ⟩
  (DtoList n pf L.++ ((toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c)) L.++ flatten n x
    ≡⟨ cong (λ h → (DtoList n pf L.++ h) L.++ flatten n x) (L.++-assoc (toList m) _ _ ∙ cong (toList m L.++_) (L.++-assoc (flatten n a) _ _)) ⟩
  (DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b L.++ flatten n c) L.++ flatten n x ∎


open import Cubical.Structures.Function
open import Cubical.Structures.Pointed
open import Cubical.Structures.Constant

module _ {A : Type} (isSetA : isSet A) where
  headQ : TreeQ A → Maybe A
  headQ = SQ.rec (isOfHLevelMaybe 0 isSetA) head′ λ a b p → sym (head-toList a) ∙ cong headL p ∙ head-toList b

  consQ : A → TreeQ A → TreeQ A
  consQ x = SQ.rec squash/ (_/_.[_] ∘ cons′ x) λ a b p → eq/ (cons′ x a) (cons′ x b) (toList-cons′ x a ∙ cong (x ∷_) p ∙ sym (toList-cons′ x b))

  snocQ : TreeQ A → A → TreeQ A
  snocQ xs x = SQ.rec squash/ (_/_.[_] ∘ λ ys → snoc′ ys x) (λ a b p → eq/ _ _ (toList-snoc′ a x ∙ cong (L._++ L.[ x ]) p ∙ sym (toList-snoc′ b x))) xs

  TreeQ-Flex2S : Flex2S A
  TreeQ-Flex2S = TreeQ A , (headQ , consQ , snocQ)

  toList' = TreeQ≃List isSetA .fst

  toList∼ : (a : Tree A) → toList' _/_.[ a ] ≡ toList a
  toList∼ a = refl

  head∼ : (a : TreeQ A) → headQ a ≡ headL (toList' a)
  head∼ = elimProp (λ x → isOfHLevelMaybe 0 isSetA _ _) (λ a → sym (head-toList a))

  cons∼ : (x : A) (a : TreeQ A) → toList' (consQ x a) ≡ x ∷ (toList' a)
  cons∼ x = elimProp (λ x → isOfHLevelList 0 isSetA _ _) (toList-cons′ x)

  snoc∼ : (a : TreeQ A) (x : A) → toList' (snocQ a x) ≡ snocL (toList' a) x
  snoc∼ a x = elimProp (λ a → isOfHLevelList 0 isSetA (toList' (snocQ a x)) (snocL (toList' a) x)) (λ a → toList-snoc′ a x ∙ snocL-++ _ x) a

  TreeQ∼List : TreeQ-Flex2S ≃[ Flex2S-EquivStr A ] List-Flex2S A
  -- here Agda's very unhelpful "either you unfold all the way down or you don't unfold at all" policy makes the types of the holes unreadable, so you just kind of guess them
  TreeQ∼List = TreeQ≃List isSetA , head∼ , cons∼ , snoc∼

  TreeQ-Flex2S-List : TreeQ-Flex2S ≡ List-Flex2S A
  TreeQ-Flex2S-List = Flex2S-ΣPath A _ _ TreeQ∼List



record Flex-2Sided-Law {A} (Flex : Flex2S A) : Type₁ where
  Arr = Flex .fst
  op  = Flex .snd

  hd : Arr → Maybe A
  hd = op .fst

  cons : A → Arr → Arr
  cons = op .snd .fst

  snc : Arr → A → Arr
  snc = op .snd .snd

  field
    sccs : ∀ (x : A) y xs → snc (cons x xs) y ≡ cons x (snc xs y)
    hc   : ∀ (x : A) xs   → hd (cons x xs)    ≡ just x

open Flex-2Sided-Law using (sccs; hc)

List-Law : {A : Type} → Flex-2Sided-Law (List-Flex2S A)
List-Law .sccs x y xs = refl
List-Law .hc   x   xs = refl

TreeQ-Law : {A : Type} → (isSetA : isSet A) → Flex-2Sided-Law (TreeQ-Flex2S isSetA)
TreeQ-Law isSetA = subst Flex-2Sided-Law (sym (TreeQ-Flex2S-List isSetA)) List-Law


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
