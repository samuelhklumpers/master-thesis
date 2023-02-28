IRI doesn't have this, but maybe this can be reformulated in terms of QERs

```
{-# OPTIONS --cubical #-}

module RelationFromChaos where

private variable
  A B : Set
  x y z w : A
```

Suppose we are given a pair of functions f : A → B and g : B → A.
When we are applying SIP or representation independence, we of course have that f and g are inverses, yielding an equivalence and by SIP a path.

In the example of ListQueue≃BatchedQueue, we have that f and g aren't exactly inverses, but instead f is injective and g is surjective.
Quotienting the BatchedQueue by the appropriate relation improves them to an equivalence.

Note that we actually did not have to find this appropriate relation:
it is the same as prop. truncating the fibers of g, or relating x ~ y iff g x = g y.

What happens if we drop the assumptions on f and g?
Propositionally truncating the fibers of g would not work, as they need not stay contractible like before.

Taking (only) x ~ y iff g x = g y and z ~ w iff f z = f w
would not work: x and y can be in the fiber of f over z, while their fibers in g need not be identical.



Not yet sure whether only having f or both f and g makes a big difference.
90We can do two things:

Number one is forming the relations
```
module _ {A B : Set} (f : A → B) (g : B → A) where
  data ChaosL : A → A → Set
  data ChaosR : B → B → Set

  -- that's not very prop. of you
  data ChaosL where
    refL : ChaosL x x
    conL : ChaosR x y → ChaosL (g x) (g y)
    tran : ChaosL x y → ChaosL y z → ChaosL x z
    symm : ChaosL x y → ChaosL y x

  data ChaosR where
    refR : ChaosR x x
    conR : ChaosL x y → ChaosR (f x) (f y)
    tran : ChaosR x y → ChaosR y z → ChaosR x z
    symm : ChaosR x y → ChaosR y x
```
and then subtyping A and B to the images of g and f respectively.
Which doesn't seem very helpful.

Instead if we only consider f, we can force it to become an equivalence more directly.
That is, we truncate the fibers, and restrict to the image.

In fact, part of this is already worked out in the cubical library.
We still have to force f to become an embedding, after which we can use isEquivEmbeddingOntoImage.
```
open import Prelude
open import Cubical.Functions.Embedding
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Relation.Binary.Base
open import Cubical.Functions.Image
open BinaryRelation

module _ {dom cod : Type} (isSetCod : isSet cod) (f : dom → cod) where
  fiberRel : dom → dom → Type
  fiberRel x y = f x ≡ f y

  dom' : Type
  dom' = dom / fiberRel

  fiberTrunc : dom' → cod
  fiberTrunc = SQ.rec isSetCod f (λ a b r → r)

  isPropValuedFiberRel : isPropValued fiberRel
  isPropValuedFiberRel a b = isSetCod (f a) (f b)

  isEquivRelFiberRel : isEquivRel fiberRel
  isEquivRel.reflexive  isEquivRelFiberRel = λ _ → refl
  isEquivRel.symmetric  isEquivRelFiberRel = λ _ _ → sym
  isEquivRel.transitive isEquivRelFiberRel = λ _ _ _ → _∙_
  
  lemma : ∀ x y → fiberTrunc x ≡ fiberTrunc y → x ≡ y
  lemma = elimProp2 (λ x y → isPropΠ (λ _ → squash/ x y)) λ a b → eq/ a b 

  fiberTruncIsEmbedding : isEmbedding fiberTrunc
  fiberTruncIsEmbedding x y = isEquiv-proof
    where
    isEquiv-proof : ∀ {x y} → isEquiv (cong {x = x} {y = y} fiberTrunc)
    equiv-proof isEquiv-proof p = (lemma _ _ p , isSetCod _ _ _ p) , (λ q → isPropΣ (squash/ _ _) (λ _ → isOfHLevelSuc 2 isSetCod _ _ _ _) _ _)

  crude = restrictToImage fiberTrunc
  
  crudeIsEquiv : isEquiv crude
  crudeIsEquiv = isEquivEmbeddingOntoImage (fiberTrunc , fiberTruncIsEmbedding)
```

Not sure if this is helpful, unless you have that f is either injective or surjective,
and you're willing to define respectively cod or dom to be the image or quotient.
E.g. uncurry _++_ : List × List → List is surjective and defining Batch = List × List / fiberRel would be fine.
