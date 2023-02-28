```
{-# OPTIONS --cubical #-}

module Whynot01 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ

open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Data.Equality as Eq renaming (eqToPath to path) using ()
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum as S
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; Bool→Type)

import Cubical.Data.Equality as Eq

private variable
  ℓ : Level
  A B : Type ℓ
  x y : A
```

We have some examples in which we construct new containers from numeral systems, either by calculating the container from a set of laws, or by ornamenting the system to carry elements.
In our examples, we start from the (zero-less) n-ary numbers. However, in general, each type of cardinality ℕ evidently defines a "suitable" numeral system.

Let us explore some reasonable, some unreasonable examples, and try to find the extent to which this idea can be pushed.

--* Cantor
A short example illustrates why (al)most (all) types A ≃ ℕ are not suitable.
Most types under consideration so far are "linear" in the sense that their constructors are recursive in at most one argument.

The first numeral system which comes to mind featuring (heavy) branching is:

data Cantor : Set where
  zero : Cantor
  pair : Cantor → Cantor → Cantor

We can define e : Cantor ≃ ℕ using the (bijective!) Cantor pairing function π : ℕ × ℕ → ℕ.
It follows that

e zero       = 0
e (pair x y) = 1 + π (e x , e y)

defines a bijection.

However, not only is this complicated to convert into a container, it already fails to be a (useful) numeral system.
In particular, the successor function already demonstrates a catastrophic O(n) best case performance.

We won't give a proof, but the intuition that any type with branching recursion suffers from the same drawbacks can be explained.
Namely
1. each such type necessarily defines a pairing function
2. the "optimal" pairing function is bit-interleaving

Here "optimal" is used in the sense that for n, m we have π (n , m) ~ n * m (you can't fit a n×m rectangle into less than a n×m rectangle).
Still, bit-interleaving suffers from the same issues, having to inspect both branches of each constructor relatively deeply for each successor operation.
Thus, any other branching numeral system would make matters even worse.


--* Sparse
Not all hope is lost, and there are some more conventional ways of describing numbers using more clever types.
For example, rather than storing all digits in a row (densely), we could describe binary numbers by giving the offsets of the non-zero digits.
Such numeral systems are referred to as sparse representations, and some examples of their associated containers are described by [Okasaki].

These form a very interesting class of datastructures to study both for their theory, and their efficiency in practice.
However, we will leave these aside for now, and attempt to establish another "negative" result.


--* Quotients
Notable is that the most obvious replacement for ℕ, the ordinary binary numbers, do _not_ work for our purposes, as they are redundant.
Later on, we will encounter more redundant systems, and ways to deal with their redundancy while still making use of their other properties.

In this section we investigate an alternative way to erase the redundancy from a numeral system,
and find out why it fails.

Without further ado, let's define the ordinary binary numbers.
We can do this in a couple of ways, for example as lists of digits
```
infix 10 0b_ 1b_

data DL : Type where
  nb  : DL
  0b_ : DL → DL
  1b_ : DL → DL
```

We read these as little-endian naturals (i.e., least significant digit first, or from right-to-left).
For example, we express the number `10` as `0b 1b 0b 1b nb`.

Indeed, this representation turns out to be horribly redundant!
Namely, adding a `0b` on the right (equivalently, having leading zeroes) does not change the value of a number.

Using our new found power (`--cubical`), we have multiple methods of resolving this problem.
We will be quotienting by a relation, ensuring that redundant expressions, like `0b 1b 0b nb`, become equivalent to non-redundant ones, in this case `0b 1b nb`.

We could use
```
{-
R : DL → DL → Type
R nb     nb     = ⊤
R nb     (0b x) = R nb x
R nb     (1b _) = ⊥
R (0b x) nb     = R x nb
R (0b x) (0b y) = R x y
R (0b _) (1b _) = ⊥
R (1b _) nb     = ⊥
R (1b _) (0b _) = ⊥
R (1b x) (1b y) = R x y
-}
```
But in this case, defining a datatype is both more compact and has the added benefit of being able to pattern match on `R a b`
```
infix 8 _R_

data _R_ : DL → DL → Type where
  nb-R  : nb R nb
  r-R   : nb R x → nb R 0b x
  l-R   : x R nb → 0b x R nb
  0b-R  : x R y  → 0b x R 0b y
  1b-R  : x R y  → 1b x R 1b y
```

Remark: here `R` defines a binary relation on `DL`, relating `0b x` to `nb`, provided `x R nb`.
In particular, this let's us unfold things like (0b 0b nb) R nb step-by-step, i.e., nb R nb ⇒ (0b nb) R nb ⇒ (0b 0b nb) R nb.

Note also that `R` satisfies some nice (and some necessary) properties like symmetry and congruence for constructors
```
sym-R : ∀ x y → x R y → y R x
sym-R .nb .nb nb-R = nb-R
sym-R .nb .(0b _) (r-R r) = l-R (sym-R nb _ r)
sym-R .(0b _) .nb (l-R r) = r-R (sym-R _ nb r)
sym-R .(0b _) .(0b _) (0b-R r) = 0b-R (sym-R _ _ r)
sym-R .(1b _) .(1b _) (1b-R r) = 1b-R (sym-R _ _ r)
```

Taking the quotient
```
Bin = DL / _R_
```
ensures that any term with leading zeros becomes equal to one with none,
and yields the equalities we would expect from non-redundant binary numbers, like:
```
example : Path Bin [ 1b 0b 0b nb ] [ 1b nb ]
example = eq/ _ _ (1b-R (l-R (l-R nb-R)))
```

Clearly any "natural" number type should be isomorphic to ℕ,
so let's prove this! For this, we define some helpers:
```
module Digits where
  nb-not-0b : ∀ x → nb ≡ 0b x → ⊥
  nb-not-0b x p = subst (λ { nb → ⊤ ; (0b y) → ⊥ ; (1b y) → ⊤ }) p tt

  nb-not-1b : ∀ x → nb ≡ 1b x → ⊥
  nb-not-1b x p = subst (λ { nb → ⊤ ; (0b y) → ⊤ ; (1b y) → ⊥ }) p tt

  0b-not-1b : ∀ x y → 0b x ≡ 1b y → ⊥
  0b-not-1b x y p = subst (λ { nb → ⊤ ; (0b z) → ⊤ ; (1b z) → ⊥ }) p tt

  shiftr : DL → DL
  shiftr nb     = nb
  shiftr (0b x) = x
  shiftr (1b x) = x

  0b-inj : ∀ x y → 0b x ≡ 0b y → x ≡ y
  0b-inj x y p = cong shiftr p

  1b-inj : ∀ x y → 1b x ≡ 1b y → x ≡ y
  1b-inj x y p = cong shiftr p

  discreteDL : Discrete DL
  discreteDL nb nb = yes refl
  discreteDL nb (0b y) = no (nb-not-0b _)
  discreteDL nb (1b y) = no (nb-not-1b _)
  discreteDL (0b x) nb = no (nb-not-0b _ ∘ sym)
  discreteDL (0b x) (0b y) with discreteDL x y
  ... | yes p = yes (cong 0b_ p)
  ... | no ¬p = no (¬p ∘ 0b-inj _ _)
  discreteDL (0b x) (1b y) = no (0b-not-1b _ _)
  discreteDL (1b x) nb = no (nb-not-1b _ ∘ sym)
  discreteDL (1b x) (0b y) = no (0b-not-1b _ _ ∘ sym)
  discreteDL (1b x) (1b y) with discreteDL x y
  ... | yes p = yes (cong 1b_ p)
  ... | no ¬p = no (¬p ∘ 1b-inj _ _)
  
  isSetDL : isSet DL
  isSetDL = Discrete→isSet discreteDL

  -- successor operation on DL,
  -- note that because DL is binary, the term grows a lot slower in the number of applications of suc than it would in ℕ!
  suc : DL → DL
  suc nb     = 1b nb
  suc (0b x) = 1b x
  suc (1b x) = 0b (suc x) -- carry the bit

  -- interpret a list of binary digits as a natural
  ⟦_⟧ : DL → ℕ
  ⟦ nb ⟧   = 0
  ⟦ 0b x ⟧ = 2 ℕ.· ⟦ x ⟧
  ⟦ 1b x ⟧ = 1 ℕ.+ 2 ℕ.· ⟦ x ⟧

  -- "⟦_⟧ is a homomorphism of natural numbers"
  ⟦⟧-suc : ∀ x → ⟦ suc x ⟧ ≡ ℕ.suc ⟦ x ⟧
  ⟦⟧-suc nb     = refl
  ⟦⟧-suc (0b x) = refl
  ⟦⟧-suc (1b x) = (cong (2 ℕ.·_) (⟦⟧-suc x)) ∙ ·-suc 2 ⟦ x ⟧

  -- going back is very easy using suc!
  fromℕ : ℕ → DL
  fromℕ ℕ.zero    = nb
  fromℕ (ℕ.suc n) = suc (fromℕ n)
```

Evidently, a natural number should satisfy fromℕ ⟦ x ⟧ ≡ x, for which the following lemma is essential, but clearly fails already at 0
```
  -- fromℕ-2· : ∀ n → fromℕ (2 ℕ.· n) ≡ 0b fromℕ n
  -- fromℕ-2· ℕ.zero    = {!nb ≡ 0b nb!}
  -- fromℕ-2· (ℕ.suc n) = {!nice try!}
```

This is precisely because nb ≡ 0b nb cannot automatically hold in DL, which is why adding it as a path to Bin _does_ make Bin a proper natural number type.
So, let us pack up all operations on DL into operations on Bin.
```
module Binary where
  -- some boilerplate lifting operations from DL to Bin (not sure if this is necessary or could be smoother)
  Bin-0b : Bin → Bin
  Bin-0b = setQuotUnaryOp 0b_ λ _ _ r → 0b-R r

  Bin-1b : Bin → Bin
  Bin-1b = setQuotUnaryOp 1b_ λ _ _ r → 1b-R r

  suc : Bin → Bin
  suc = setQuotUnaryOp Digits.suc p
    where
    -- note that non-trivial operations on quotients require us to provide (non-trivial) coherences.
    -- particularly, maps out of quotients cannot violate the relation 
    p : ∀ a a' → a R a' → Digits.suc a R Digits.suc a'
    p .nb .nb nb-R = 1b-R nb-R
    p .nb .(0b _) (r-R r) = 1b-R r
    p .(0b _) .nb (l-R r) = 1b-R r
    p .(0b _) .(0b _) (0b-R r) = 1b-R r
    p .(1b _) .(1b _) (1b-R r) = 0b-R (p _ _ r)
    
  ⟦_⟧ : Bin → ℕ
  ⟦_⟧ = SQ.rec isSetℕ Digits.⟦_⟧ p
    where
    p : ∀ a b → a R b → Digits.⟦ a ⟧ ≡ Digits.⟦ b ⟧
    p .nb .nb nb-R = refl
    p .nb .(0b _) (r-R r) = cong (2 ℕ.·_) (p _ _ r)
    p .(0b _) .nb (l-R r) = cong (2 ℕ.·_) (p _ _ r)
    p .(0b _) .(0b _) (0b-R r) = cong (2 ℕ.·_) (p _ _ r)
    p .(1b _) .(1b _) (1b-R r) = cong (λ n → 1 ℕ.+ 2 ℕ.· n) (p _ _ r)

  ⟦⟧-suc : ∀ x → ⟦ suc x ⟧ ≡ ℕ.suc ⟦ x ⟧
  ⟦⟧-suc = SQ.elimProp (λ _ → isSetℕ _ _) Digits.⟦⟧-suc

  fromℕ : ℕ → Bin
  fromℕ = [_] ∘ Digits.fromℕ

  -- the lemma which fails for DL now holds in Bin, exactly by the path we inserted
  fromℕ-2· : ∀ x → fromℕ (2 ℕ.· x) ≡ Bin-0b (fromℕ x)
  fromℕ-2· ℕ.zero    = eq/ nb (0b nb) (r-R nb-R)
  fromℕ-2· (ℕ.suc x) = 
    fromℕ (2 ℕ.· ℕ.suc x)    ≡⟨ cong fromℕ (·-suc 2 x) ⟩
    fromℕ (2 ℕ.+ 2 ℕ.· x)    ≡⟨ cong (λ k → suc (suc k)) (fromℕ-2· x) ⟩
    Bin-0b (fromℕ (ℕ.suc x)) ∎

  fromℕ-1+2· : ∀ n → fromℕ (1 ℕ.+ 2 ℕ.· n) ≡ Bin-1b (fromℕ n)
  fromℕ-1+2· ℕ.zero    = refl
  fromℕ-1+2· (ℕ.suc n) = 
    fromℕ (1 ℕ.+ 2 ℕ.· ℕ.suc n)   ≡⟨ cong (fromℕ ∘ ℕ.suc) (·-suc 2 n) ⟩
    fromℕ (ℕ.suc (2 ℕ.+ 2 ℕ.· n)) ≡⟨ cong (suc ∘ suc) (fromℕ-1+2· n) ⟩
    Bin-1b (fromℕ (ℕ.suc n))      ∎
```

We can now piece some of these lemmas together to get some nice properties of Bin
```
-- the actual proof of equivalence between our binary naturals and the unary naturals
-- (no univalence, yet)
Bin≃ℕ : Bin ≃ ℕ
Bin≃ℕ = isoToEquiv (iso ⟦_⟧ fromℕ sec ret)
  module Bin≃ℕ where
    open Binary

    sec : section ⟦_⟧ fromℕ
    sec ℕ.zero    = refl
    sec (ℕ.suc x) = ⟦⟧-suc (fromℕ x) ∙ cong ℕ.suc (sec x)

    ret : retract ⟦_⟧ fromℕ
    ret = elimProp (λ _ → squash/ _ _) go
      module ret where
        go : ∀ a → fromℕ Digits.⟦ a ⟧ ≡ [ a ]
        go nb     = refl
        go (0b a) = fromℕ-2· Digits.⟦ a ⟧ ∙ cong Bin-0b (go a)
        go (1b a) = fromℕ-1+2· Digits.⟦ a ⟧ ∙ cong Bin-1b (go a)
```
Great!

The obvious index type is defined like
```
{-
Index′ : Bin → Type
Index′ x = Σ[ y ∈ Bin ] (x Binary.> y)
-}
```

However, this is a bit clumsy.
We can try to give a more practical implementation
```
data Index : DL → Type where
  0t0 : ∀ {x} → Index x → Index (0b x)
  0t1 : ∀ {x} → Index x → Index (0b x)
  
  1t0 : ∀ {x} → Index x → Index (1b x)
  1t1 : ∀ {x} → Index x → Index (1b x)
  1h0 : ∀ {x}           → Index (1b x)
```

and prove that this is a suitable index type
```
{-
-- If you wanted to
Index-0b : ∀ x → Index (0b x) ≡ Index x ⊎ Index x
Index-0b x = ua (fun , equiv)
  where
  fun : Index (0b x) → Index x ⊎ Index x
  fun (0t0 ix) = inl ix
  fun (0t1 ix) = inr ix

  equiv : isEquiv fun
  equiv-proof equiv (inl x) = (0t0 x , refl) , λ { (0t0 y , p) → {!!} ; (0t1 y , p) → {!!} }
  equiv-proof equiv (inr x) = {!!}

2×⊥ : ⊥ ⊎ ⊥ ≡ ⊥
2×⊥ = ua ((λ { (inl ()) ; (inr ()) } ) , record { equiv-proof = λ () })

⊥-strict : ∀ {ℓ} {A : Type ℓ} → (A → ⊥) → A ≃ ⊥
⊥-strict f = uninhabEquiv f λ () 

Index-nb : ∀ x → x R nb → Index x ≡ ⊥
Index-nb x r = ua (⊥-strict (h x r))
  where
  h : ∀ x → x R nb → Index x → ⊥
  h nb r ()
  h (0b x) (l-R r) (0t0 ix) = h x r ix
  h (0b x) (l-R r) (0t1 ix) = h x r ix

re-index-Bin : ∀ x → Fin ⟦ x ⟧ ≃ Index x
re-index-Bin nb     = {!!}
re-index-Bin (0b x) = {!!}
re-index-Bin (1b x) = {!!}
-}
```

But this isn't an index for Bin yet.

We get to choose:
1a. admit that there was a better way to describe Bin which let's us define IndexB : Bin → Type
1b. define a choice of representative Bin → DL
2. prove way more lemma's about Index : DL → Type

```
{-
-- ¬ (isSet Type) so we pay the price 
IndexB : Bin → Type
IndexB [ a ] = Index a
IndexB (eq/ a b r i) = h a b r i
  where
  h : ∀ a b (r : a R b) → Index a ≡ Index b
  h .nb .nb nb-R i = Index nb
  h .nb .(0b _) (r-R r) i = {!ah so that's why!}
  h .(0b _) .nb (l-R r) i = {!!}
  h .(0b _) .(0b _) (0b-R r) i = {!!}
  h .(1b _) .(1b _) (1b-R r) i = {!!}

IndexB (squash/ b b₁ p q i i₁) = {!!}
-}
```

```
unreduce : DL → DL
unreduce nb     = nb
unreduce (0b x) = 0b (0b x)
unreduce (1b x) = 0b (1b x)

reduce : DL → DL
reduce nb     = nb
reduce (0b x) = unreduce (reduce x)
reduce (1b x) = 1b (reduce x)

represent : Bin → DL
represent = SQ.rec Digits.isSetDL reduce go
  where
  go : ∀ a b → a R b → reduce a ≡ reduce b
  go .nb     .nb     nb-R     = refl
  go .nb     .(0b _) (r-R r)  = cong unreduce (go _ _ r)
  go .(0b _) .nb     (l-R r)  = cong unreduce (go _ _ r)
  go .(0b _) .(0b _) (0b-R r) = cong unreduce (go _ _ r)
  go .(1b _) .(1b _) (1b-R r) = cong 1b_ (go _ _ r)

IndexB : Bin → Type
IndexB x = Index (represent x)

hm : ∀ x → Index (unreduce x) → Index x ⊎ Index x
hm x ix = h x (unreduce x) Eq.refl ix
  where
  h : ∀ x w → unreduce x Eq.≡ w → Index w → Index x ⊎ Index x
  h nb (0b w) () ix
  h nb (1b w) () ix
  h (0b x) nb () ix
  h (0b x) (0b .(0b x)) Eq.refl (0t0 ix) = inl ix
  h (0b x) (0b .(0b x)) Eq.refl (0t1 ix) = inr ix
  h (0b x) (1b w) () ix
  h (1b x) nb () ix
  h (1b x) (0b .(1b x)) Eq.refl (0t0 ix) = inl ix
  h (1b x) (0b .(1b x)) Eq.refl (0t1 ix) = inr ix
  h (1b x) (1b w) () ix

IndexB-0b : ∀ x → IndexB [ 0b x ] → IndexB [ x ] ⊎ IndexB [ x ]
IndexB-0b (0b x) ix = hm _ ix
IndexB-0b (1b x) (0t0 ix) = inl ix
IndexB-0b (1b x) (0t1 ix) = inr ix
```

In conclusion, it runs, but by no means smoothly.
```
module BinaryV where
  data Vec (A : Type) : Bin → Type where
    nil :                                 Vec A [ nb ]
    0v  :     Vec A [ x ] → Vec A [ x ] → Vec A [ 0b x ]
    1v  : A → Vec A [ x ] → Vec A [ x ] → Vec A [ 1b x ]

  -- didn't think this would work
  cons : A → Vec A x → Vec A (Binary.suc x)
  cons x nil        = 1v x nil nil
  cons x (0v v w)   = 1v x v w
  cons x (1v y v w) = 0v (cons x v) (cons y w)

  lookup : Vec A x → IndexB x → A
  lookup (0v {x = x} v w) ix = S.rec (lookup v) (lookup w) (IndexB-0b x ix)
  lookup (1v x v w) (1t0 ix) = lookup v ix
  lookup (1v x v w) (1t1 ix) = lookup w ix
  lookup (1v x v w) 1h0      = x
```
