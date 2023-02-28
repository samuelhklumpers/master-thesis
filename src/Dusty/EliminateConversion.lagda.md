```
{-# OPTIONS --cubical #-}

module EliminateConversion where

open import Prelude
open import Leibniz.Base
open import Leibniz.Properties

import Cubical.Data.Nat as N
open import Cubical.Data.Nat.Properties
```

Often we're in a situation where we have naive definition of some algorithm on one side, and an optimized definition on the other side. Then we usually proceed by proving equivalence of the definitions, so that we can show correctness of the optimized definition.

Wouldn't it be nice if we got the optimized definition and its correctness for free?
Let's try.

```
record Σ' {a b} (A : Set a) (B : A → Set b) : Set (ℓ-max a b) where
  constructor s'_
  field
    {fst} : A
    snd : B fst

open Σ'

infix 1 s'_

Point : {X : Type} → X → Type
Point {X = X} x = Σ' X λ y → x ≡ y

_+'_ : Leibniz → Leibniz → Leibniz
x +' y = fromℕ (⟦ x ⟧ N.+ ⟦ y ⟧)

+'-e : ∀ x y → Point (x +' y)
-- comment this
+'-e x y = s' refl -- dummy
{-
-- and uncomment this, to remark that, unsurprisingly, +'-o now is both correct and as "optimized" as you wanted it to be 
+'-e 0b     y = s' ℕ≃L.sec y
+'-e (x 1b) 0b = s' cong (λ k → suc (fromℕ k)) (+-zero (⟦ x ⟧ N.+ (⟦ x ⟧ N.+ 0))) ∙ fromℕ-1+2· ⟦ x ⟧ ∙ cong _1b (ℕ≃L.sec x)
+'-e (x 1b) (y 1b) = s' {!1 + from (2 * x + 1 + 2 * x) ... lots of lemmas ... 2 + 2 * from (x + y) ... x + y 2b !}
+'-e (x 1b) (y 2b) = s' {!on the bright side, the lemmas are about ℕ and the ringsolver probably makes short work of large parts!}
+'-e (x 2b) y = {!!}
-}

+'-o : Leibniz → Leibniz → Leibniz
+'-o x y = fst (+'-e x y)
```

In short, it is hard to imagine there is a way to just "optimize away conversions", unless you have a solver ready.
The syntax kind of works if you're defining something as the result of some rewriting.
(Although I imagine this is already happening over at Calculating Datastructures).
