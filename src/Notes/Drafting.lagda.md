```
{-# OPTIONS --cubical #-}
```

0. Log (reverse order so I have to scroll less far)

--* b: 2023-02-22
This week:
- try to coax abstract nonsense to give us algebra isos (~> a.4.1)
- rediscover the implicit sum type                      (~> a.2.2)
- try to compute ornaments over equivalences            (~> a.1.5)
- investigate the relation nesting <-> branching
- make [Bool]/~ work (modulo comfort) (it works only if you can represent the classes, i.e. if you could already make it work on a different type)
- try to upgrade decrement : n -ary → n -ary to tail : n -ary → n -ary (~> a.1.3)


1. Questions
1.1. Going down instead of up
It feels like a.3.1. is thinking upside down: while it would be nice to be able to implement an Upgrade while not destroying everything but the coherence property, but a priori there is no good reason upgrades should preserve much at all. Furthermore restricting the implementation seems unlikely to work given the complexity of (2.1), which makes it seem like upgrades are hopeless without unrestricted functions.

Q: What about the other direction? Can we implement a generic upgrade, which upgrades a function to all ornaments, and then instantiate the properties for specific ornaments from this magical object?
A: Unanswered (the title [Programming Metamorphic Algorithms] sounds like it does something like this, but I'm not certain)

1.2. When initial algebras are strict
Q: But when are they strict?
A: Some ideas written in
```
import Initiality
```

Here is the line of thought:
  1. rather than proving X ≃ Y, we can try to prove they're both initial algebras for the same F
  2. if X = μ D then X is trivially initial for Ḟ D
  3. if X is also strict, then merely an algebra map Y → X suffices to show X ≃ Y

Hence a short look into category theory began.
  a. The algebras of F : C → C are the algebras over the free monad T of F, provided C is nice.
  b. The category C^T of algebras over T is a topos when T has a left-adjoint or something.
  c. A topos is a ccc, and initial objects in ccc's are strict.
  d. Hence, the initial algebra of F would be strict.

However (b) rarely happens, consider F : X ↦ 1 + X, which doesn't preserve (co-)limits so is not an adjoint.
Maybe there are some milder conditions.

1.3.
Q: When is the algebra map forced by the algebra structures?
A: A perhaps more reasonable stab (than 1.2) is to show that in

       F f
  F X ----> F Y
  | ^        |
α | | s      | β 
  v |        v
   X  ---->  Y
       f

we have that α is a split epi (with section s), and F is such that f is completely determined by s.

As an example, this happens for F : X ↦ 1 + X: we have
- f (α (inl tt)) = β (inl tt)
- f (α (inr x))  = β (inr (f x))
which, provided that when s x = inr x', then x' < x, defines a structural (?) recursion,
such that f x = f (α (s x)).

1.4.
Q: Can we extend descriptions to HITs
A: Probably, a path constructor is just σ I (λ i → ṿ []) with some flair after all.


2. Answers
a.2.2. (cont.)
Equivalent to defining and then proving correctness, but can be written more compactly (probably less comfortable in practice).
```
import EliminateConversion
```

2.1. Upgrades (a.1.3. (cont.))
Remark that Nary-Lists are virtually equivalent to Josh Ko's binomial heaps.
Upgrade decrement to tail (unfinished).
```
import Nary-List
```

2.2. Moving around Ornaments (a.1.5. (cont.))
Some setup is performed in
```
import MobileOrnaments
```
Take-aways from this small experiment are:
- non-trivial
  - clearly keeping the same indices fails by a counting argument
- squashing branches
  - if the base types are both linear, then the recursive structure should not be an obstacle
- probing
  - using some facts and imposing some conditions (e.g. the square commutes), we **can** probe the constructors that are forced for the algebra maps,
    it almost looks like we can probe the required fields and indices for the constructors as well

Clearly if two "things" are going to be equivalent, they are also going to **contain** the same "things", so I hope we can compute the fields (the σ's) from "preservation of contents".
This sounds a bit like Traversable <-> Normal, but a bit more chaotic and hard to imagine.


3. Misc
```
import Whynot01
```

--* a: 2023-02-15
1. Questions
1.1. Can we transport proofs of functions on unary naturals to binary naturals?
A: Yes (3.1).

1.2. Can we derive (efficient) implementations from simple specifications?
A: Requires a bunch of work even for simple examples, but no failure yet (2.2).

1.3. Can we lift `_+_` to `_++_`
A: Yes (Transporting Functions across Ornaments)

1.4. Can we get associativity of `_++_` from associativity of `_+_`?
A: No! (3.1).

1.5 For `(X Y : Desc I)`/`(X : Orn D, Y : Orn E)` when is `(mu X ~ mu Y)`/`(mu ceil(X) ~ mu ceil(Y))`?
For `X : Orn D` and `mu D ~ mu E`, what is the corresponding `Y : Orn E`?
A: Unanswered. (4.1).

1.6. Does (1.1) generalize to other datastructures?
A: Probably.

1.7. Can we generalize calculating datastructures a bit?
A: Yes! (at least the case of nested n-ary trees) (2.3). 

1.8. Can we get a more categorical picture of the state of affairs? E.g. `Vec A n` is a monoid displayed over the monoid of natural numbers. (Check this in the Cubical discord).
A: Unanswered.

1.9. Can we instantiate the appropriate relations on `X` and `Y` to get `X / ~X = Y / ~Y` from their description as (co)-algebras, or simply maps `f, g: X <-> Y`?
A: The former is unanswered. The answer to the latter is somewhat trivially positive (2.4).

1.10. Can we make SIP work with records as structures?
A: I hope so. (Simply describe a record `X` such that `X ~ mu XDesc`, where `mu XDesc` is workable with SIP).

2. Positive answers
2.1. Proof transport

This might sound a bit dream-like, so some (simple) demonstration is in order.

```
import Leibniz.Properties
```

2.2. Optimizing definitions from specifications

Can we define functions (on more intricate types) by their behaviour (on simpler types), without sacrificing too much efficiency?
We can try:

pred : Leibniz -> Leibniz
pred = fromN . pred . [[_]]

pred n = fromN (pred [[ n ]])

pred 0b     = fromN (pred [[ 0b ]]) = 0
pred (x 1b) = fromN (pred [[ 1b x ]]) = fromN (pred (1 + 2 * [[ x ]])) = fromN (2 * [[ x ]]) = double x
pred (x 2b) = fromN (pred [[ 2b x ]]) = fromN (pred (2 + 2 * [[ x ]])) = fromN (1 + 2 * [[ x ]]) = x 1b

Ok..., but what about double?

double : Leibniz -> Leibniz
double n = fromN (double [[ n ]])

double 0b     = 0
double (x 1b) = fromN (double [[ 1b x ]]) = fromN (double (1 + 2 * [[ x ]])) = fromN (2 + 2 * [[ double x ]]) = double x 2b
double (x 2b) = fromN (double (2 + 2 * [[ x ]])) = fromN (2 + 2 + 2 * 2 * [[ x ]]) = fromN (2 + 2 * (1 + 2 * [[ x ]])) = x 1b 2b

Not sure if this is very convincing.


2.3. Ornamenting n-ary binary numbers.

Smooth sailing modulo encoding overhead.
Succesfully described n-ary (zeroless) binary numbers and ornaments on them to get their associated index type and array type.

```
import Nary
```

2.4. From a cycle to a relation

```
import RelationFromChaos
```

As we can see, it works, but at best it saves you some space by not having to write down the forget and the relation separately. 
That is, if you're trying to hit your intended datatypes on the nose, you're going to have to prove that your map was injective/surjective to begin with, which is just as much work as proving the equivalence directly.



3. Negative answers
3.1. Lifting properties along ornaments.

Pretty disastrous.
E.g. associativity need not be preserved by arbitrary coherent lifts, like `_+_` -> `_++_` does not stop us from swapping elements.

Likewise, the type of patching `_+_` to vector `_++_` pretty clearly still allows such pathological patches (I think, actually decoding the type is virtually impossible).

One would need something impractically strong like a traversable (and more) to hope to lift properties.
Perhaps if we restrict to morphisms that cannot see contents?



4. Unanswered
4.1. Relations between ornaments from equivalences of their fixpoints.

For the former, hardly anything reduces. For the latter, similarly `mu D ~ mu E` says very little about `D`, whence correspondence between `X` and `Y` is hardly controlled by this. 



A.
1. Introduction

Upholding the tradition of getting free things: doing less work for more.
While, hopefully, not sacrificing the safety or efficiency of our programs,
or even improving them.

Examples of generalizability can be on a foundational level, like having polymorphism, be it parametric or ad-hoc (duck-typing doesn't count).
Another way to get generality can be through generics/reflection (meta-programming).

For a part, safety automatically happens when you don't have duck-typing, pointers, unsafe coercion, incomplete pattern matching/non-total functions, non-termination, ...
You can get more safety/certainty about your code by testing it, but why would you extensively (and never exhaustively) test your code, when you can also "just" explain why the code works?
We can achieve this by constraining the types of our programs to enforce their behaviour, or by adapting different (more methodical) methods of "synthesizing code".

The catch is that we're in (Cubical) Agda so efficiency isn't something that happens in the code we write per se.
The aim is to start from simple and safe implementations, to switch to more efficient/complex implementations,
but then generalize the safety proofs from the simple to the complex case.
After this, we can (attempt) to erase the (Cubical) from Agda, and then agda2hs the Agda into Haskell and hope it still runs, but is now safe and quick.

