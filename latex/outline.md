# 1. Intro

Programming is hard, but using the right tools can make it easier. Logically, much time and effort goes into creating such tools. Because it hard to memorize the documentation of a library, we have code suggestion; to read code more easily, we have code highlighting; to write tidy code, we have linters and formatters; to make sure code does what we hope it does, we use testing; to find the right tool for something, we have IDEs. 

Globally speaking, this thesis looks at how we can make written code more easy to verify and to reuse, or even to generate from scratch. We hope, that this lets us spend more time on writing code rather than tests, spend less time repeating similar work, and save time by writing more powerful code.

We use the language Agda, of which the dependent types form the logic we use to specify and verify the code we write. In our approach, we describe a part of the language inside the language itself, allowing us to reason about the structure of other code using code itself. Such a description of code can then be evaluated to generate usable code, also allowing us to discuss how we can transform one piece of code into another by comparing the descriptions of both pieces.

More specifically, our efforts are directed at describing, and then generating and verifying a class of container types from number systems. The idea is that container types, which evidently are types that contain elements of other types, often ``look like'' a number system by squinting a bit. Consequently, types of that class of containers are known as numerical representations. This leads us to our research question:

> Can numerical representations be described as modifications of number systems, and how does this make verifying their properties easier?

Our contribution will be to rework part of the existing theory and techniques of descriptions, modifications, and generics to make it possible to simultaneously fit number systems and numerical representations into this theory in a comfortable way.
 
To make the research question formal, we first need to properly define the concepts of descriptions and modifications of descriptions.

# 2. Background

We extend upon and make heavy use of existing work for generic programming and ornaments, so let us take a closer look at the nuts and bolts to see what all the concepts are about.

## 2.1 Agda

We formalize all of our work in the programming language Agda. Agda is, like Haskell, a functional programming language.

[ focusing on how functions can (de)construct data ]: #  

While we will only occasionally reference Haskell, those more familiar with Haskell may look at Agda as an extension (in a very broad sense) of Haskell, allowing less functions, but more complex types. This allows to express more constructs in more detail, while (hopefully) ruling out more incorrect implementations.

In this section, we will explain and highlight some parts of Agda which will be necessary to discuss the work in later sections.

### 2.1.1 Data in Agda   
At the level of ordinary (i.e., generalized algebraic) datatypes, Agda is close to Haskell. In both languages, one can define objects using data declarations, and interact with them using function declarations. For example

:memo: data Bool

The constructors of this type, false and true, can be read as lists of requirements to create a value of Bool. In this case, both require nothing, which declares that Bool always has exactly two elements. We can then define functions on Bool. Other than directly using a value of Bool in an expression, we can also pattern match on Bool. If we pattern match on a datatype, then we must provide definitions for each possible case of that type\footnote{This is enforced by the coverage checker.}. As an example, the conditional operator is defined by

:memo: if\_then\_else

We can also define a type representing numbers as a datatype

:memo: data \bN

The constructor zero expresses that \bN always has an element 0, and succ expresses that for each element n, there is also an element representing n + 1. In conclusion, \bN represents the positive integers, henceforth naturals. Similarly, we can pattern match on \bN to define the comparison operator

:memo: \_<\_

Now one of the cases contains a recursive instance of \bN: the coverage checker and termination checker ensure that we still define \_<\_ for all possible combinations of numbers. Essentially, these checks ensure that any valid definition by pattern matching corresponds to a valid proof by cases and induction\footnote{Also note that in this case we actually have a simultaneous induction on two arguments. This is tolerated when the arguments decrease lexicographically. Put in other words, a simultaneous induction must consist of a nested sequence of valid inductions.}.

We could now directly define lists of natural numbers, but then we would have to repeat this for lists of booleans and all other types. Using parameters, we can instead define a family of types. Introducing a parameter in a datatype corresponds to abstracting the body of the type over a free variable, by applying this abstraction one gets a type for each value of the parameter.

With parameters, we define a type of lists for each type:

:memo: data List

If we insert a bunch of things in a list, we can also pick one of them out

:memo: lookup

but this is not amazing, as we are relying on the Maybe type

:memo: Maybe

to handle the failing case where the index falls outside of the list. Note that checking

:memo: length

beforehand amounts to the same, substituting false for nothing.

If the length of the list is known, then we already know for which indices lookup will succeed and for which it will not. To encode and use this information we will need indexed types. Like parameters, indices add a variable to the context of a data body, but unlike parameters, indices can influence the availability of constructors. This difference can be employed to constrain the possible values of a variable from the type level. As an example, we can index Bool over itself

:memo: HBool

This creates the singleton type HBool, in which knowing the type of a variable of HBool uniquely fixes its value: HBool true can only be constructed by htrue, while HBool false can only be constructed by hfalse.

Applying this principle to naturals and lists, we can create a pair of types

:memo: Fin

:memo: Vec

We see that Fin 0 contains no elements, and the only vector in Vec 0 is the empty vector [], also containing no elements. Likewise, Fin (suc n) contains one more element than Fin n, and a vector in Vec (suc n) is necessarily a vector Vec n with one more element. From this we conclude that Fin n is exactly the type of suitable indices into a Vec n. 

Furthermore, dependent functions let us bind variables in type signatures, and use them in later types. This allows us to define

:memo: lookup 

by letting the size of the index type vary with the length of the vector. The case in which we would return nothing for lists, is now actually impossible and can be discarded. Lookup always succeeds for vectors, demonstrating that vectors are correct-by-construction. However, this does not yet prove that lookup always returns the right element.

If we want to express claims like ``inserting x at i and looking up i returns x'' we need more logic.


### 2.1.2 Proving in Agda

Defining vectors, we saw how knowing the index of a variable can constrain the set of values it is in. We can use this to define a datatype in which the index actually determines whether there is any value, or none at all:

:memo: \_\equiv\_

We can only have refl : Eq a b if and only if a is equal to b, justifying the use of the \_\equiv\_ symbol. The claim that lookup is indeed correct can be written as the dependent function type

:memo:

:warning: and now prove it, or something?

:memo: toList

## 2.2 Numerical representations

:warning: Nat \to Vec


## 2.3 Descriptions

In 2.1 we completed a quadruple of types (\bN, List, Vec, Fin) which have a nice interaction (length : List A \to \bN, toList : Vec A n \to L A, lookup : Vec A n \to Fin n \to A). This construction works because \bN, List, Vec, and Fin all have the same shape, and one can expect it to work for similar quadruples. However, shape is not (yet) defined inside our language, so in this section, we will set out to explain the groundwork making this expectation sensible.

To describe datatypes, and their shapes, we will define a type of descriptions. 

[ Descriptions have existed for longer than I have. ]: #

Comparing this to the usual type theoretic terminology in which a type of types like Type is called a universe, we can think of a type of descriptions as a universe. Each description, or code, should then represent a type via a function known as an interpretation \mu : U \to Type. In very short terms, a universe-construction can be as simple as a pair (U, \mu : U \to Type).

Let us walk through some concrete universe constructions to make this less foggy. We will start from very simple classical description, building up our way to more and more general types, until we reach a universe in which we can describe the (\bN, List, Vec, Fin) quadruple, which, as a bonus, gives some insight into the meaning of datatypes.

We can define a basic universe by assuming the existence of two types 0 and 1, and requiring that the universe is closed under sums and products:

:memo: U = 0 1 + x 

:memo: U -> Type

This is enough to encode Bool

:memo: BoolD

The types 0 and 1 are finite, and sums and products of finite types are also finite. Hence, U is the universe of finite types. This also means that \bN cannot fit in U.

To accomodate \bN, we need to be able to express types that recursively refer to themselves. We can amend U to allow such types, just by adding a code representing a recursive occurrence.

:memo: U2 = 0 1 \rho + x

However, as a consequence, \mu cannot be defined as simply as it was for U, since in \mu (1 + \rho), we need to know that the whole type was 1 + \rho while processing \rho. Thus, we split \mu into two parts: one interpretation

:memo: \[[\_\]] 

acting like \mu would for U, where X represents ``the current type'', and a fixpoint

:memo: \mu : U2 \to Type

which closes the open interpretation and returns the resultant type, by inserting itself for ``the current type'' X. Now representing \bN is as simple as

:memo: NatD

[ :warning: mu is actually pretty fundamental (the mathematical way of viewing it) ]: #

One downside of starting from U2 is that the formation from + x does not mirror the way we define types manually very well. We redefine U2 in an equivalent way by using the fact that polynomials have canonical forms as sums of products. On top of this, we can let the left hand side of x be any type to allow ordinary fields\footnote{:warning: yes this is a problem and yes we fix this when parameters}.

:memo: SOP

Using this universe requires us to split functions on descriptions into multiple parts, but makes going between the representation and concrete types straightforward.

We also note that this encoding of fields has the downside of introducing ``larger descriptions'' into the universe, which make the universe no longer foldable, in contrast to the earlier iterations. By introducing parameters in the right way\footnote{The right way for us, that is. If a foldable universe means nothing to you, there are simpler encodings for parameters and indices, which are recorded in the appendix (ref).}, we can restore the foldability of the universe as a bonus.

This also means that we have to handle types with many parameters, so let us first describe the bookkeeping gadget we will use for this. In a parametrized type, parameters can refer to bound values of preceding parameters. The parameters of a type are thus a sequence of types depending on eachother. We call such a sequence a telescope, which we can describe as

:memo: tel

We can also evaluate a telescope to get the type representing a valid choice of parameters

:memo: eval

By extending upon telescopes, we can bound arguments using nearly same mechanism.

:memo: Tel2

:warning: Tel2 gets a parameter

:memo: ExTel

:memo: the gang

:memo: new eval

Introducing this into the universe yields

:memo: U3

:memo: U3 \to Type \to Type

in which the function S \to U2 is now replaced by U3 (.. \rhd S), preserving the dependence in the variable telescope while avoiding the higher order argument. In this universe, we can present List as

:memo: ListD

Finally, we can work indexed types into the universe by abstracting over indices. Recall that in native Agda datatypes, a choice of constructor can fix the indices of the recursive fields and the resultant type, so we encode

:memo: U4

with

:memo: \mu U4 \to Type \to I \to Type

In this universe, we can define finite types and vectors

:memo: Fin

:memo: Vec

so we can compare the structures in the quadruple (\bN, List, Fin, Vec) by looking at their descriptions.

As a bonus, we get some parts of generic programming. For example, we can define the generic fold as a function which takes a description, and returns the fold for the interpretation

:memo: fold

[ :warning: functions, for free and for all (idk what i wanted to type here) ]: #


## 2.4 Ornaments


In this section we will introduce the concepts we need to compare datatypes via their descriptions.

Comparing descriptions, \bN and List are almost the same, except that List has a parameter and an extra field \bN does not have. We could say that we can form the type of lists by starting from \bN and adding this parameter and field, while keeping everything else the same. If we form a binary relation on descriptions consisting of all such valid transformations, we will end up with a type of ornaments.

[ remark, ornForget is never epi because of \sigma 0 ]: #

Conceptually, an ornament from type A to type B represents that B can be formed from A. Consequently, we expect that if there is such an ornament, then we get a function ornForget : B \to A. This materializes the idea that B is then a more elaborate version of A, and that if one can construct a term of B, then one always gets a term of A. 

This function ornForget also makes it easy to generalize relating functions between two similar types. For example, if we have ornForget : List A \to \bN, then the statement that concatenation preserves length becomes a special case of stating that concatenation and ornForget commute.

[ also, recomputation, but appendix ]: #

[ :warning: we present a simplified version, the complicated one will appear in due time ]: #

Let us now define a type of ornaments as a datatype, so that we may prove that there is an ornament from \bN to List. We give a simplified account here, a more general account can be found in 3.2.

But what do we expect the signature of ornForget to be? Certainly it should be something like

:memo: ornForget?

but we are missing some pieces of information. To be precise, before we can undo the ornament, we must be able to compute the parameters and indices of the less complicated type from those of the more complicated type. We conclude that an ornament from Desc \GG J to Desc \GD K also has to encode functions \GD \to \GG and K \to J. The complete signature should thus be

:memo: ornForget

We can now define ornaments on descriptions by acting on each constructor separately

:memo: DescOrn

:warning: ConOrn the how and the why

:memo: ConOrn

:warning: the relation N-L

:warning: the relation L-V


## 2.5 Proof transport

An unfortunate consequence of proving about types via their description is that the resulting proofs now refer to the fixpoint, which is distinct but isomorphic to the user-defined type. Working with the fixpoint directly is a far cry from user-friendly, so we cannot reasonably expect the fixpoint to replace the original type. 

Instead, we will have to ``rebase'' the proofs from the fixpoint to the original type. This can be done mechanically using reflection, but that would not be very portable and would force developers of types of descriptions to also write a macro specialized to their descriptions.

From mathematical intuition, this should also not be necessary. A group theorist would not repeat a (group theoretic) proof for isomorphic groups, a topologist would not repeat a (topological) proof for homeomorphic spaces, so a type theorist should not have to repeat a proof (which is automatically type theoretic if you are in a proof assistant) for isomorphic types.

However, if we expect that if A \\~- B would imply that for all predicates P, P A iff P B, then A actually has to be equal to B. (Consider P A = (A \equiv B)). While this simply is not the case in the base theory we are working in, the Cubical extension does make this true.

The following section is not essential to understand the later sections and can be skipped, as it mainly goes into more detail on how Cubical changes the theory and how that affects our later constructions. In short, if we can mechanically derive a description from a type, then we can get an equivalence and proof transport for free, but on the other hand, we will have to avoid axiom K in constructions.


### 2.5.1 SIP

:warning: cubical paths

:warning: not K

:warning: ua: why our work wants cubical

:warning: SIP

:warning: proof transport



# 3 Calculating datastructures using Ornaments

In this part we return to the matter numerical representations. With 2.3 in mind, we can rephrase part our original question to ask

> Can numerical representations be described as ornaments on their number systems?

Let us look at a numerical representation presented as ornament in action.

[ actually much like calculating datastructures in concept, but very different in practice ]: #

## 3.1 Calculating vectors

Let us put the calculation from 2.2 in the framework of ornaments. Recall the Peano naturals \bN and their description

:memo: NatD

which we will use as reference number system. The associated container then has constructors

:memo: ListD

:warning: calculate

But before we can answer the question in full generality, we need ask ourselves what kind of ornaments and number systems this question applies to. Construction similar to the one in this section (e.g., the construction from binary numbers \to binary trees \to indexed binary trees) will generally fit in any setup of descriptions and ornaments supporting (recursive) fields and indices. However, there are also other less regular datatypes which we can still recognize as numerical in nature.


## 3.2 Finger trees

:warning: finger trees are pretty cool for a lot of reasons, but for us it is sufficient to remark that they are also the simplest way to get fast cons on both sides

:warning: what are they though

:warning: they do not fit at all

:warning: so we need more stuff

:warning: nested datatypes

:warning: composites

:warning: number systems


## 3.2 Descriptions

:warning: let's blast out the descriptions

:warning: recap: what do we want? (leaf, field, recursive, composite)

:warning: how do we cram number systems in? bundles

:warning: go (list everything)

## 3.3 Ornaments

:warning: match everything, add/remove field, add/remove recursive field, add/remove description field, ornament over ornament


## 3.4 The calculation

:warning: number systems

:warning: the trie ornament

:warning: the problem (no more free things, everything becomes hard)

# 4 Discussion

:warning: the trie ornament is hard to prove about

:warning: nesting rather than branching

:warning: folds don't give folds over parts

:warning: composites complicate the indexed variant

:warning: the index type becomes more awkward than with big sigmas

# 5 Related work

# A Appendix

:warning: The other way of parameters-indices