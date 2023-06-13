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

To inspect a datatype and manipulate its values safely, we have to represent the datatype internally. This can be done by defining another datatype encoding how datatypes can be formed, henceforth description, together with a function which assigns meanings to this encoding, henceforth interpretation. We will start from an encoding which captures only a small set of types, and work towards an encoding of parametrized indexed types.

\begin{code}[hide]
module Finite where
\end{code}
\begin{code}
  data Desc : Type where
    𝟘 𝟙      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
Each of the constructors of this description represents a type-former for the described universe. In this case, the universe only contains the finite types; the meaning of the type formers should be evident from the interpretation:
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
but to encode a type like \bN we need a different setup. Consider the definition
\begin{code}
data ℕ : Type where
  zero  : ℕ
  suc   : ℕ → ℕ 
\end{code}
we can interpret this as the declaration \texttt{ℕ ≃ ⊤ ⊎ ℕ,} and formally, ℕ is indeed the least fixpoint of this equation. Intuitively, this tells us that ℕ can be formed by applying ⊤ ⊎ a countable number of times to ⊥. More generally, we see that recursive types are the fixpoints of polynomial functors
\begin{code}[hide]
module Recursive where
\end{code}
\begin{code}
  data Desc : Type where
    𝟙 ρ      : Desc
    _⊕_ _⊗_  : Desc → Desc → Desc
\end{code}
Now we will have to split the interpretation and the fixpoint, where the interpretation now translates a description to a polynomial functor
\begin{code}
  ⟦_⟧ : Desc → Type → Type
  ⟦ 𝟙      ⟧ X = ⊤
  ⟦ ρ      ⟧ X = X
  ⟦ D ⊕ E  ⟧ X = (⟦ D ⟧ X) ⊎ (⟦ E ⟧ X)
  ⟦ D ⊗ E  ⟧ X = (⟦ D ⟧ X) × (⟦ E ⟧ X)
\end{code}
mapping 𝟙 to the constant 1 polynomial, ρ to the variable x polynomial, and ⊕ and ⊗ to the ordinary polynomial sum and product. (Conspicuously, 0 is missing, but you can see that ⊥ is not. After all, μ ρ has no values). Taking the fixpoint gives the actual type
\begin{code}
  data μ (D : Desc) : Type where
    con : ⟦ D ⟧ (μ D) → μ D
\end{code}
so that we can describe ℕ as
\begin{code}
  ℕD  : Desc
  ℕD  = 𝟙 ⊕ ρ
\end{code}
To make describing complex types more practical we can merge ρ and ⊗, and add a variant σ of ⊗ allowing arbitrary types in descriptions
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
In σ, we ask for a function S → Desc rather than just a Desc, modelling a Desc with a bound variable of S. We interpret σ S D as Σ[ s ∈ S ] ⟦ D s ⟧ X.

In this universe we can describe types in which the fields be either X, the type itself, or another type S. For example, we can describe List using an external parameter
\begin{code}
  ListD : Type → Desc
  ListD A = 𝟙 ⊕ (σ A λ _ → ρ 𝟙) 
\end{code}
We will soon see how we can internalize parameters, but since internalizing indices is easier, we will tackle indices first.

We should note that there are two strategies we can use to describe an indexed type. First, we can define a description of a type indexed by I to simply be a function I → Desc, yielding a universe of index-first types. Second, we can pull the index completely into Desc, and let 𝟙 declare the index at the leaf of a constructor, more closely resembling Agda's datatypes. Both have their advantages and disadvantages, mainly, index-first datatypes are more space efficient. We opt however for the second option, because as we will see later, this allows us to keep descriptions "relatively small" (i.e., something like foldable) and more flexible in their levels.
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
Now 𝟙 i says that this branch constructs a term of X i, while ρ i asks for a recursive field X i. As Desc I describes a type indexed by I, which is a function I → Type, we also have to interpret Desc I as an indexed functor 
\begin{code}
  ⟦_⟧ : Desc I → (I → Type) → (I → Type)
  ⟦ 𝟙 j    ⟧ X i = i ≡ j
  ⟦ ρ j D  ⟧ X i = X j × ⟦ D ⟧ X i
  ⟦ σ S D  ⟧ X i = Σ[ s ∈ S ] ⟦ D s ⟧ X i
  ⟦ D ⊕ E  ⟧ X i = ⟦ D ⟧ X i ⊎ ⟦ E ⟧ X i
\end{code}
Applying an interpretation to an index i asks for the constructors at i. We see that by interpreting 𝟙 j as an equality, we ensure that if we ask for i, then we also must get something at index i. In this universe we can also describe vectors
\begin{code}
  VecD : Type → Desc ℕ
  VecD A = (𝟙 zero) ⊕ (σ ℕ λ n → σ A λ _ → ρ n (𝟙 (suc n)))
\end{code}
making use of the variable binding in σ to state that if we get a vector of length n, then we can construct a vector of length suc n.

The observant reader might have noticed that we claim I → Desc does not give small descriptions, but still allow for S → Desc. We can fix this issue at the same time we implement parameters, keeping a form of variable binding. We could implement types with a single parameter by interpreting to "endofunctors" Type → I → Type, adding another type-former accessing the parameter. This is however a bit less flexible than we want, does not distinguish between types with actually no parameters and a type applied to ⊥, nor allows us to refer to fields in the parameters.

We will first need some structure expressing the kinds of parameters that we can have. We could try using List Type, but this rules out types like Σ (A : Type) (B : A → Type). Instead, we use a telescope, a list of types which does capture the dependency. To define a type depending on the preceding telescope, we define telescopes and their meaning by induction-recursion 
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
so a telescope can either be empty, or be formed from a telescope and a type in the context of that telescope, where the context is defined as
\begin{code}[hide]
  ⟦ ∅      ⟧tel = ⊤
  ⟦ Γ ▷ S  ⟧tel = Σ ⟦ Γ ⟧tel S
\end{code}
However, to deal with variables, we will also need to be able to describe variable telescopes. This means that while the parameter telescope in a description stays constant, the variable telescope grows independently when we add more σ's. We can represent this by parametrizing telescopes over a type
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
We define a shorthand Γ ⊢ A for type of S, representing a value of A in context Γ. By changing ⟦\_⟧tel to depend on a value of P as
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
can access all values of Γ, and can be treated as an extension of Γ. To interpret them, we define
\begin{code}
  ⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
  ⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel
\end{code}
To make use of this we also split ⊕ and Desc, making Desc a list of constructors, in line with actual Agda datatypes
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
replacing I by V ⊢ I in 𝟙 and ρ allows the index of a constructor or argument to depend on the preceding fields, of which the values are made accessible by appending them to the context as V ▷ S in σ. Finally, we interpret this as
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
