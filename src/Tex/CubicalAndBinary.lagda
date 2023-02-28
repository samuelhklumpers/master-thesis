\documentclass[../Main.tex]{subfiles}


\begin{document}
Let us quickly review the small set of features in Cubical Agda that we will be using extensively throughout this article.\footnote{\cite{cuagda} gives a comprehensive introduction to cubical agda.} At the surface, there are two significant differences. The downside, being that 
\begin{code}
{-# OPTIONS --cubical #-} 
\end{code}
also implies the negation of axiom K, which in turn sabotages both some termination checking and some universe levels. And, more obviously, we get saddled with the proof obligation that our types are sets should we use certain constructions.

\begin{code}[hide]
module Tex.CubicalAndBinary where

open import Cubical.Foundations.Prelude hiding (sym; funExt)
open import Leibniz.Base
open import Leibniz.Properties
import Cubical.Data.Nat as N

private variable
    A B : Type
    x y : A
    f g : A → B
\end{code}

The upside is that we get a primitive notion of equality, and get access to univalence which both drastically cut down the investment required to both show more complex structures to be equivalent (at least when compared to non-cubical) and also use this equivalence meaningfully. Here, equality arises not (directly) from the indexed inductive definition we are used to, but rather from the presence of the interval type \AgdaPrimitiveType{I}. This type represents a set of two points \AgdaInductiveConstructor{i0} and \AgdaInductiveConstructor{i1}, which are considered ``identified'' in the sense that they are connected by a path. To define a function out of this type, we also have to define the function on all the intermediate points, which is why such a function represents a ``path''. Terms of other types are then considered identified when there is a path between them.

As an added benefit, this different perspective gives intuitive interpretations to some proofs of equality, like
\AgdaTarget{sym}
\begin{code}
sym : x ≡ y → y ≡ x
sym p i = p (~ i)
\end{code}
where \AgdaFunction{∼\_} is the interval reversal, swapping \AgdaInductiveConstructor{i0} and \AgdaInductiveConstructor{i1}, so that \AgdaFunction{sym} simply reverses its path argument.

Furthermore, because we can now interpret paths in records and function differently, we get a host of ``extensionality'' for free. For example, a path in $A \to B$ is indeed a function which takes each $i$ in \AgdaPrimitiveType{I} to a function. Using this, proving function extensionality becomes easy enough: 
\AgdaTarget{funExt}
\begin{code}
funExt : (∀ x → f x ≡ g x) → f ≡ g 
funExt p i x = p x i
\end{code}

Finally, univalence tells us that when two types are equivalent, then they can also be identified. \todo{put the ua thing here}
For our purposes, we can treat equivalences as the ``HoTT-compatible'' generalization of bijections. In particular, type isomorphisms like $1 \to A \simeq A$ actually become equalities $1 \to A \equiv A$, such that we can transport proofs along them. We will demonstrate this by a slightly more practical example.


\subsection{Binary numbers}
We will take a look the underlying shapes of lists and trees, namely, the (Peano) natural numbers and the (Leibniz) binary natural numbers. We define the Leibniz naturals as follows:
\ExecuteMetaData[../Leibniz/Base.tex]{Leibniz}
Here, the \AgdaInductiveConstructor{0b} constructor encodes 0, while the \AgdaInductiveConstructor{\_1b} and \AgdaInductiveConstructor{\_2b} constructors respectively add a 1 and a 2 bit, under the usual interpretation of binary numbers:
\ExecuteMetaData[../Leibniz/Base.tex]{toN}
Clearly \AgdaDatatype{ℕ} and \AgdaDatatype{Leibniz} ``are the same'', so let us summarize this proof. First, we can also interpret a number in \AgdaDatatype{ℕ} as a binary number by repeating the successor operation on binary numbers:
\ExecuteMetaData[../Leibniz/Base.tex]{bsuc}
\ExecuteMetaData[../Leibniz/Base.tex]{fromN}
To show that the operations are inverses, we observe that the interpretation respects successors
\ExecuteMetaData[../Leibniz/Properties.tex]{toN-suc}
and that the inverse respects even and odd numbers\todo{line too long}
\ExecuteMetaData[../Leibniz/Properties.tex]{fromN-1}
The wanted statement follows
\ExecuteMetaData[../Leibniz/Properties.tex]{N-iso-L}
but since we now have a bijection, we also get an equivalence\todo{fix this symbol}
\ExecuteMetaData[../Leibniz/Properties.tex]{N-equiv-L}
Finally, by univalence, we can identify the Peano and Leibniz naturals
\ExecuteMetaData[../Leibniz/Properties.tex]{N-is-L}

\todo{is this too much code and too little explanation at once?}

\subsection{Structure Identity Principle}
Using the path \AgdaFunction{ℕ≡L} we can already prove some otherwise difficult properties, e.g.,
\ExecuteMetaData[../Leibniz/Properties.tex]{isSetL}
It would be a shame if we defined binary numbers and identified them with the naturals and then proceeded to not use them. So, let us define addition. Clearly, a sensible implementation should agree with natural addition under the interpretations. We could take
\begin{code}
BinOp : Type → Type
BinOp A = A → A → A

_+′_ : BinOp Leibniz
_+′_ = subst BinOp ℕ≡L N._+_
\end{code}
But this would be rather inefficient, incurring an $O(n + m)$ overhead when adding $n + m$, so we could better define addition directly.

Inspired by the ``use-as-definition'' notation from \cite{calcdata}, we define the following syntax for giving definitions by equational reasoning
\todo{define it}
\begin{code}

\end{code}
with which we can define
\todo{define plus}
\begin{code}

\end{code}

We see that as a consequence, the pairs $(\AgdaDatatype{ℕ}, \AgdaFunction{N.+})$ and $(\AgdaDatatype{Leibniz}, \AgdaFunction{+})$ are equal. More generally, we can view a type $X$ combined with a function \AgdaFunction{\_\cdot\_:}$ X \to X \to X$ as a kind of structure, which in fact coincides with a magma. Now we can see that two magmas are identical if their underlying types $X$ are, and their operations \AgdaFunction{\_\cdot\_} agree modulo their identification. This observation is further generalized by the Structure Identity Principle (SIP), formalized in \cite{iri}. This principle describes a procedure to derive for a structure the appropriate notion of ``structured equivalence'' $\iota$. The $\iota$ is such that if structures $X, Y$ are $\iota$-equivalent, then they are identified.

In our case, we have just shown that the \AgdaFunction{\_+\_} magmas on \AgdaDatatype{ℕ} and \AgdaDatatype{Leibniz} are equal, hence associativity of \AgdaFunction{\_+\_} for \AgdaDatatype{Leibniz} follows immediately from that on \AgdaDatatype{ℕ}.
\todo{prove it}
\begin{code}

\end{code}
\end{document}