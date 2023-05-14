\begin{code}
module Enumeration.Approach1 where

open import Prelude hiding (rec)
open import Data.List renaming (map to mapL)
open import Data.List.Instances
open import Effect.Monad
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open RawMonad {ℓ-zero} listMonad using (_>>=_)

\end{code}

%<*hierarchy>
\begin{code}
Hierarchy : Type → Type
Hierarchy A = ℕ → List A
\end{code}
%</hierarchy>

\begin{code}

mapH : (A → B) → Hierarchy A → Hierarchy B
mapH f V n = mapL f (V n)

data In {A : Type} (a : A) : List A → Type where
  here  : ∀ {as}             → In a (a ∷ as)
  there : ∀ {b as} → In a as → In a (b ∷ as)

Complete : Hierarchy A → Type
Complete V = ∀ a → Σ[ n ∈ ℕ ] In a (V n)

Unique : Hierarchy A → Type
Unique V = ∀ a n m (i : In a (V n)) (j : In a (V m)) → Σ[ p ∈ n ≡ m ] PathP (λ i → In a (V (p i))) i j 

\end{code}

%<*buildertype>
\begin{code}
Builder : (A B : Type) → Type
Builder A B = Hierarchy A → Hierarchy B
\end{code}
%</buildertype>

\begin{code}


\end{code}

%<*pure>
\begin{code}
pure : B → Builder A B
pure x _ zero    = [ x ]
pure x _ (suc n) = []
\end{code}
%</pure>

\begin{code}

\end{code}

%<*rec>
\begin{code}
rec : Builder A A
rec B zero    = []
rec B (suc n) = B n
\end{code}
%</rec>

\begin{code}

interleave : List A → List A → List A
interleave [] ys = ys
interleave (x ∷ xs) ys = x ∷ interleave ys xs

\end{code}

%<*alternative>
\begin{code}
_⟨∣⟩_ : Builder A B → Builder A C → Builder A (B ⊎ C)
(B₁ ⟨∣⟩ B₂) V n = interleave (mapL inl (B₁ V n)) (mapL inr (B₂ V n))
\end{code}
%</alternative>

\begin{code}

prod : List A → List B → List (A × B)
prod []       ys       = []
prod (x ∷ xs) []       = []
prod (x ∷ xs) (y ∷ ys) = (x , y) ∷ interleave (mapL (x ,_) ys) (prod xs (y ∷ ys))

\end{code}

%<*pair>
\begin{code}
pair : Builder A B → Builder A C → Builder A (B × C)
pair B₁ B₂ V n =
     (downFrom (suc n) >>= λ i → (prod (B₁ V n) (B₂ V i)))
  ++ (downFrom n       >>= λ i → (prod (B₁ V i) (B₂ V n)))
\end{code}
%</pair>

\begin{code}

\end{code}

%<*Desc>
\begin{code}
data Desc : Set where
  one : Desc
  var : Desc
  _⊗_ : (D E : Desc) → Desc
  _⊕_ : (D E : Desc) → Desc

⟦_⟧ : Desc → Set → Set
⟦ one ⟧ X = ⊤
⟦ var ⟧ X = X
⟦ D ⊗ E ⟧ X = ⟦ D ⟧ X × ⟦ E ⟧ X
⟦ D ⊕ E ⟧ X = ⟦ D ⟧ X ⊎ ⟦ E ⟧ X

data μ (D : Desc) : Set where
  con : ⟦ D ⟧ (μ D) → μ D
\end{code}
%</Desc>

\begin{code}

\end{code}

%<*builder>
\begin{code}
builder : ∀ {D} D' → Builder (μ D) (⟦ D' ⟧ (μ D))
builder one     = pure tt
builder var     = rec
builder (D ⊗ E) = pair (builder D) (builder E)
builder (D ⊕ E) = builder D ⟨∣⟩ builder E
\end{code}
%</builder>

\begin{code}

\end{code}

%<*gbuilder>
\begin{code}
gbuilder : ∀ D → Builder (μ D) (μ D)
gbuilder D V = mapH con (builder D V)
\end{code}
%</gbuilder>

\begin{code}

\end{code}

%<*build>
\begin{code}
iterate : ℕ → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = f (iterate n f x)

build : Builder A A → Hierarchy A
build B n = iterate (suc n) B (const []) n

hierarchy : ∀ D → Hierarchy (μ D)
hierarchy D = build (gbuilder D)
\end{code}
%</build>

\begin{code}
\end{code}

%<*TreeD>
\begin{code}
TreeD : Desc
TreeD = one ⊕ (var ⊗ var)

TreeH = hierarchy TreeD
\end{code}
%</TreeD>

\begin{code}
Tree′ = μ TreeD

data Tree : Type where
  leaf : Tree
  node : Tree → Tree → Tree

conversion : Tree′ → Tree
conversion (con (inl _))       = leaf
conversion (con (inr (l , r))) = node (conversion l) (conversion r)

trees : ℕ → List Tree
trees n = mapL conversion (TreeH n)

trees-2 : List Tree
trees-2 =
\end{code}
%<*trees-2>
\begin{code}
    node (node leaf leaf) (node leaf leaf)
  ∷ node (node leaf leaf) leaf
  ∷ node leaf             (node leaf leaf)
  ∷ []
\end{code}
%</trees-2>

\begin{code}
\end{code}
