```
{-# OPTIONS --cubical #-}

module MobileOrnaments where

open import Prelude hiding (⌊_⌋)
open import ProgOrn.Ornaments

open import Data.List
import Data.Vec as V

import Cubical.Data.Nat as N
import Data.Fin as Fin
open import Data.Bool
open import Data.Fin hiding (toℕ)
```

--* The question
Open question:
  We have e : ℕ ≃ Leibniz and ℕ = μ NatD, Leibniz = μ LeibnizD,
  and List A = μ ⌊ Nat-ListOrn ⌋ for Nat-ListOrn : OrnDesc ⊤ ! NatD.

  Where does L-TreeOrn  come from?


--* No simple answer
Clearly there is no L-TreeOrn : OrnDesc ⊤ ! LeibnizD and an e' : List A ≃ Tree A such that e' has e as underlying function.
Namely length xs = n enforces that size (e' xs) = n, while depth (e' xs) = ceillog n
Looking at the progression n = 0..3 points out the failure: the 0b constructor carries 0 elements, 1b carries 1, 2b carries 2, so e 3 = 0b 1b 1b carries 2 elements.

The linearity of both types obstructs us from forming trees by ornamenting leibniz.
Perhaps we can get further by carefully constructing an index type.
But first, let's investigate how we can represent branching structures in a linear datatype.


--* A small note
If X and Y are inductives then they're fixpoints FX = X and GY = Y.
If X = Y, then at least F and G agree at X i.e. FX = GX.
E.g. NatF X = 1 + X and BinF X = 1 + X + X,
but clearly they're not naturally isomorphic or so.


--* Linear chains containing branching data
For this, we take inspiration from calculating datastructures and the N-ary trees experiment, in which we represent trees by linear chains of ever-growing tuples.
open import Nary

Starting from the simplest (non-trivial) case of 1-2-trees.
These can either be an empty leaf, a node with 1 element and 2 children, or a node with 2 elements and 2 children.
We can linearize this by keeping the leaf but changing the types at the nodes.
At the top node we start with the element type A, but when we encounter a node, we replace this by A × A to represent the branching of the tree.

Let's consider the case of D : Desc ⊤, in which we seek to represent D by a linearly shaped datatype.
If we recall the image of datatypes trees, then the obvious approach is to simply split the datatype into levels and carry around the shape of the tree at each level.

Suppose μ D = Zero | One (μ D) | Two (μ D) (μ D),
then we can imagine representing the term One (Two (One Zero) Zero) as the chain [tt], [[tt]], [[[tt, tt]]], [[[[tt], []]]], [[[[], []]]].
This representation is a bit clunky and inefficient, but has the advantage of generalizing to different I.

Another representation of trees can be given by chains of functions between finite types. [Sets, Models and Proofs].
In this case, we have 0 -> 1 -> 2 -> 1 -> 1, where f(x) = y signifies that x is a direct descendant of y.
(Note that this isn't optimal because the branches are always ordered)

(Let us ignore the contents of the fields to simplify the process?)
Suppose we are at some level and have n branches.
We can describe the chain with only one constructor taking in n accumulated fields, and then summing together the sizes of all recursive constructors.

```
-- level issue
{- data Accumulate : RDesc ⊤ → Type where
  leaf : ∀ {is : List ⊤}                      → Accumulate (ṿ is)
  node : ∀ {S D} → (s : S) → Accumulate (D s) → Accumulate (σ S D) -}

Accumulate : RDesc ⊤ → Type
Accumulate (ṿ is)  = ⊤
Accumulate (σ S D) = Σ S λ s → Accumulate (D s)

consize : (d : RDesc ⊤) → (a : Accumulate d) → ℕ
consize (ṿ is)  a = length is
consize (σ S D) a = consize (D (fst a)) (snd a)

nested : Desc ⊤ → Desc ℕ
nested d n = σ (V.Vec (Accumulate (d tt)) n) λ a →
  let m = V.foldl (λ _ → ℕ) (λ xs x → consize (d tt) x N.+ xs) 0 a
  in σ (Fin m → Fin n) (λ _ → ṿ [ m ])

{-
module _ (SomeD : Desc ⊤) where
  Some = μ SomeD tt
  Nest = μ (nested SomeD) 1
  
  nest : Some → Nest
  nest (con x) = {!x!}
-}
```

This isn't shockingly useful, doesn't support indices (yet) and still reproduces a chunk of the branching in the index type.
However, it does indicate how we can force the morally correct transport of List over ℕ ≃ Leibniz onto something which is both linear but contains a Tree.

A short demonstration of what the nested datatype _can_ do:
```
data Three : Set where
  three1 : Three
  three2 : Three
  three3 : Three

Squiggle : Desc ⊤
Squiggle tt = σ Three λ
  { three1 → ṿ []
  ; three2 → ṿ [ tt ]
  ; three3 → ṿ (tt ∷  tt ∷ []) }

SquiggleFlat : RDesc ℕ
SquiggleFlat = nested Squiggle 1
```

--* ℕ ≃ L
With this in mind (i.e. we can cram structure into the index if necessary), we can revisit the equivalence ℕ ≃ Leibniz.
```
open import Leibniz.Properties
```

Unfolding this equivalence, we see that if we are to have length xs ≡ size (e' xs),
then for the algebra defining e we must have that the action of the algebra on Leibniz pushes the appropriate number of branches into the index of the Tree.

Ideally, we would like to combine the algebra (0b, bsuc) with adding a single element like cons into an appropriate ornamental description, with algebra, on Leibniz.
Let's write our wishlist first, and transform this into something workable later.

We have
  N   = zero | suc
  L A = nil  | cons A (L A)

the diagram to keep in mind is

       L A ..  ?
        |      .
 length |      .
        v      .
        N ---> B
           e

Clearly ?, let's name it T A, will get the same number of constructors as B
  B   = 0b     | B 1b    | B 2b
  T A = leaf ? | node1 ? | node2 ?

Let's construct the wanted equivalence and T A simultaneously

           e'
       L A -> T A
        |      |
 length |  ↻   | size
        v      v
        N ---> B
           e

For size to be forgetful it should be something like
  size (leaf ?)  = 0b
  size (node1 ?) = ? (size ?) 1b
  size (node2 ?) = ? (size ?) 2b

Since length [] = zero and e zero = 0b, we find size (e' []) = 0b, so e' [] = leaf ?

Suppose e (length xs) = ? 1b = size (e' xs) = size (node1 ?)
Suppose e (length xs) = ? 2b = size (e' xs) = size (node2 ?)

Keep in mind that T A needs to be a F X = 1 + A × X algebra,
so we need a prep' : 1 + A × T A → T A and this better comply with cons':
  e' (cons' (inl tt))       = prep' (inl tt)          = leaf
  e' (cons' (inr (x , xs))) = prep' (inr (x , e' xs))

this defines prep : A → T A → T A for which
  bsuc (size (e' xs)) = bsuc (e (length xs)) = e (suc (length xs)) = e (length (cons x xs)) = size (e' (cons x xs)) = size (prep x (e' xs))

this binds the size of the result of prep to a number again, which by the forgetful property of size enforces some constructors, hence
  prep x (leaf ?)  = node1 ?
  prep x (node1 ?) = node2 ?
  prep x (node2 ?) = node1 ?

From this, it's pretty clear from our perspective how to fill in the constructors of T A,
but it is not conclusive yet.

We might make some way flattening the shapes even harder (like Normal functors for Traversables a la McBride, but then with heterogeneous vectors and more "sizes")
