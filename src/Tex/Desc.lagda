\begin{code}[hide] 
module Tex.Desc where

open import Agda.Primitive renaming (Set to Type)
open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Relation.Binary.PropositionalEquality
open import Function.Base
\end{code}

To be able to reason about datatypes themselves, we first have to represent datatypes by another datatype.
%To inspect a datatype and manipulate its values safely, we have to represent the datatype internally.
This can be done by defining a datatype of codes instructing how datatypes can be formed, together with a function assigning the meaning to this encoding, henceforth description and interpretation respectively. We will start from an encoding which captures only a small set of types, and work towards an encoding of parametrized indexed types.
\begin{code}[hide]
module Finite where
\end{code}

We can describe the universe of finite types with the following description:
\begin{code}
  data Desc : Type where
    𝟘 𝟙      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
Each of the constructors of this description represents a type-former. In this case, the universe only contains sums and products of the 0 and 1; the meaning of the type-formers comes from the interpretation:
\begin{code}
  μ : Desc → Type
  μ 𝟘        = ⊥
  μ 𝟙        = ⊤
  μ (D ⊕ E)  = μ D ⊎ μ E
  μ (D ⊗ E)  = μ D × μ E
\end{code}
Booleans live in this universe as
\begin{code}
  BoolD : Desc
  BoolD = 𝟙 ⊕ 𝟙
\end{code}
but to encode a type like \bN{} we need a different setup. Consider the definition
\begin{code}
data ℕ : Type where
  zero  : ℕ
  suc   : ℕ → ℕ 
\end{code}
we can interpret this as the declaration \texttt{ℕ ≃ ⊤ ⊎ ℕ}, and formally \AgdaDatatype{ℕ} is indeed the least fixpoint of this equation. In category theoretic terms we would say that \AgdaDatatype{ℕ} is the initial algebra of its base functor \texttt{(⊤ ⊎\_)}.
\begin{code}[hide]
module Recursive where
  data Desc : Type
\end{code} 
Letting
\begin{code}
  ⟦_⟧ : Desc → Type → Type
\end{code}
assign base functors to descriptions, we can take the fixpoint as
\begin{code}
  data μ (D : Desc) : Type where
    con : ⟦ D ⟧ (μ D) → μ D
\end{code}
We see that if \texttt{⟦ ND ⟧} is \texttt{(⊤ ⊎\_)}, then \texttt{μ ND} satisfies the equation for \AgdaDatatype{ℕ}.

We change the codes to
\begin{code}
  data Desc where
    𝟙 ρ      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
and describe the base functors:
\begin{code}
  ⟦ 𝟙      ⟧ X = ⊤
  ⟦ ρ      ⟧ X = X
  ⟦ D ⊕ E  ⟧ X = (⟦ D ⟧ X) ⊎ (⟦ E ⟧ X)
  ⟦ D ⊗ E  ⟧ X = (⟦ D ⟧ X) × (⟦ E ⟧ X)
\end{code}
Now, \AgdaInductiveConstructor{𝟙} encodes the leaves of a datatype, and \AgdaInductiveConstructor{ρ} encodes a recursive node. The operators \AgdaInductiveConstructor{⊕} and \AgdaInductiveConstructor{⊗} are changed to act pointwise. %(Conspicuously, 0 is missing, but you can see that \AgdaDatatype{⊥} is still represented in the universe. After all, \texttt{μ ρ} has no values).
In this universe, we can define \AgdaDatatype{ℕ} by
\begin{code}
  ℕD  : Desc
  ℕD  = 𝟙 ⊕ ρ
\end{code}
To describe complex types more practically, we can merge \AgdaInductiveConstructor{ρ} and \AgdaInductiveConstructor{⊗}, and add a variant \AgdaInductiveConstructor{σ} of \AgdaInductiveConstructor{⊗}, which then represent adding a recursive and a non-recursive field respectively
\begin{code}[hide]
module NearSOP where
\end{code}
\begin{code}
  data Desc : Type₁ where
    𝟙    : Desc
    ρ    : Desc → Desc
    σ    : (S : Type) → (S → Desc) → Desc
    _⊕_  : Desc → Desc → Desc
\end{code}
In \AgdaInductiveConstructor{σ}, we ask for a function \texttt{S → Desc} rather than just a \AgdaDatatype{Desc}, modelling a \AgdaDatatype{Desc} with a bound variable of type \texttt{S}. The interpretation is similar, interpreting \AgdaInductiveConstructor{ρ} and \AgdaInductiveConstructor{σ} as a product and dependent product respectively.
%\texttt{ρ D} as \texttt{X × ⟦ D ⟧ X} and \texttt{σ S D} as \texttt{Σ[ s ∈ S ] ⟦ D s ⟧ X}.

In this universe we can describe types in which the fields be either \texttt{X}, the type itself, or another type \texttt{S}. For example, we can describe \AgdaDatatype{List} as
\begin{code}
  ListD : Type → Desc
  ListD A = 𝟙 ⊕ (σ A λ _ → ρ 𝟙) 
\end{code}
using a type parameter from outside the description. We will soon see how we can internalize parameters, but since internalizing indices is easier, we will tackle indices first.

We should note that there are two strategies we can use to describe an indexed type. First, we can define a description of a type indexed by \texttt{I} to simply be a function \texttt{I → Desc}, yielding a universe of index-first types. Second, we can pull the index completely into \AgdaDatatype{Desc}, and let \AgdaInductiveConstructor{𝟙} declare the index at the leaf of a constructor, more closely resembling Agda's datatypes. Both have their advantages and disadvantages, mainly, index-first datatypes are more space efficient. We opt however for the second option, because as we will see later, this allows us to keep descriptions ``relatively small'' (i.e., something like foldable) and more flexible in their levels.
\begin{code}[hide]
module Indexed where
  private variable
    I : Type
\end{code}
\begin{code}
  data Desc (I : Type) : Type₁ where
    𝟙    : I → Desc I
    ρ    : I → Desc I → Desc I
    σ    : (S : Type) → (S → Desc I) → Desc I
    _⊕_  : Desc I → Desc I → Desc I
\end{code}
Now \texttt{𝟙 j} says that this branch constructs a term of \texttt{X j}, while \texttt{ρ i} asks for a recursive field \texttt{X i}. As \texttt{Desc I} describes a type indexed by \texttt{I}, which is a function \texttt{I → Type}, we also have to interpret \texttt{Desc I} as an indexed functor 
\begin{code}
  ⟦_⟧ : Desc I → (I → Type) → (I → Type)
  ⟦ 𝟙 j    ⟧ X i = i ≡ j
  ⟦ ρ j D  ⟧ X i = X j × ⟦ D ⟧ X i
  ⟦ σ S D  ⟧ X i = Σ[ s ∈ S ] ⟦ D s ⟧ X i
  ⟦ D ⊕ E  ⟧ X i = ⟦ D ⟧ X i ⊎ ⟦ E ⟧ X i
\end{code}
Applying an interpretation to an index asks for the constructors at that index. We see that by interpreting \texttt{𝟙 j} as an equality, we ensure that asking for an index indeed gives that index.

In this universe we can describe vectors
\begin{code}
  VecD : Type → Desc ℕ
  VecD A = (𝟙 zero) ⊕ (σ ℕ λ n → σ A λ _ → ρ n (𝟙 (suc n)))
\end{code}
making use of the variable binding in \AgdaInductiveConstructor{σ} to state that if we get a vector of length \texttt{n}, then we can construct a vector of length \texttt{suc n}.

The observant reader might have noticed that we claim \texttt{I → Desc} does not give small descriptions, but still allow for \texttt{S → Desc}. We can fix this issue at the same time we implement parameters, keeping a form of variable binding. Implementing types with a single parameter can be done by interpreting to ``endofunctors'' \texttt{Type → I → Type}, adding another type-former accessing the parameter. To handle types with more parameters, which may depend on each other, we abstract descriptions over lists of parameters.

We will first need some structure expressing the kinds of parameters that we can have. We could try using List Type, but this rules out types like \texttt{Σ (A : Type) (B : A → Type)}. Instead, we use a telescope, a list of types which explicitly captures the dependencies. We define telescopes and their meaning by induction-recursion:
\begin{code}[hide]
module Tele where
\end{code}
\begin{code}
  data Tel : Type₁
  ⟦_⟧tel : Tel → Type
  
  data Tel where
    ∅    : Tel
    _▷_  : (Γ : Tel) (S : ⟦ Γ ⟧tel → Type) → Tel
\end{code}
A telescope can either be empty, or be formed from a telescope and a type in the context of that telescope.

Contexts are interpreted as
\begin{code}[hide]
  ⟦ ∅      ⟧tel = ⊤
  ⟦ Γ ▷ S  ⟧tel = Σ ⟦ Γ ⟧tel S
\end{code}
To deal with variables, we will also need to be able to describe variable telescopes. This means that while the parameter telescope in a description stays constant, the variable telescope grows independently when we add more \AgdaInductiveConstructor{σ}'s. We can represent this by parametrizing telescopes over a type
\begin{code}[hide]
module Parameter where
  private variable
    a : Level
    P : Type
\end{code}
\begin{code}
  data Tel (P : Type) : Type₁
  ⟦_⟧tel : Tel P → P → Type
  _⊢_ : Tel P → Type a → Type a
  Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A
  
  data Tel P where
    ∅    : Tel P
    _▷_  : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P
\end{code}
We define a shorthand \texttt{Γ ⊢ A} for the type of \texttt{S}, representing a value of \texttt{A} in context \texttt{Γ}. By changing \texttt{⟦\_⟧tel} to depend on a value of \texttt{P} as
\begin{code}
  ⟦ ∅      ⟧tel p = ⊤
  ⟦ Γ ▷ S  ⟧tel p = Σ[ x ∈ ⟦ Γ ⟧tel p ] S (p , x)
\end{code}
a telescope of the form
\begin{code}
  ExTel : Tel ⊤ → Type₁
  ExTel Γ = Tel (⟦ Γ ⟧tel tt)
\end{code}
\begin{code}[hide]
  private variable
    Γ Δ : Tel P
    V W : ExTel Γ
    I : Type
\end{code}
can access all values of \texttt{Γ}, and can be treated as an extension of \texttt{Γ}. To interpret them, we define
\begin{code}
  ⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
  ⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel
\end{code}
To make use of this we also split \AgdaInductiveConstructor{⊕} and \AgdaDatatype{Desc}, making \AgdaDatatype{Desc} a list of constructors, in line with actual Agda datatypes
\begin{code}
  data Con (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type₁
  data Desc (Γ : Tel ⊤) (I : Type) : Type₁ where
    []   : Desc Γ I
    _∷_  : Con Γ ∅ I → Desc Γ I → Desc Γ I
\end{code}
A constructor then starts off with the empty variable context, which grows as fields are added
\begin{code}
  data Con Γ V I where
    𝟙   : V ⊢ I → Con Γ V I
    ρ   : V ⊢ I → Con Γ V I → Con Γ V I
    σ   : (S : V ⊢ Type) → Con Γ (V ▷ S) I → Con Γ V I
\end{code}
replacing \texttt{I} by \texttt{V ⊢ I} in \AgdaInductiveConstructor{𝟙} and \AgdaInductiveConstructor{ρ} allows the index of a constructor or argument to depend on the preceding fields, of which the values are made accessible by appending them to the context as \texttt{V ▷ S} in \AgdaInductiveConstructor{σ}. Finally, we interpret this as
\begin{code}
  ⟦_⟧C : Con Γ V I → (⟦ Γ & V ⟧tel → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
  ⟦ 𝟙 j    ⟧C X pv i = i ≡ (j pv)
  ⟦ ρ j C  ⟧C X pv i = X pv (j pv) × ⟦ C ⟧C X pv i
  ⟦ σ S C  ⟧C X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C (X ∘ map₂ proj₁) (p , v , s) i

  ⟦_⟧D : Desc Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
  ⟦ []      ⟧D X p i = ⊥
  ⟦ C ∷ Cs  ⟧D X p i = ⟦ C ⟧C (X ∘ proj₁) (p , tt) i  ⊎ ⟦ Cs ⟧D X p i
\end{code}
with the fixpoint
\begin{code}
  data μ (D : Desc Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
    con : ⟦ D ⟧D (μ D) p i → μ D p i
\end{code}
