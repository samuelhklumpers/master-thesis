\begin{code}
{-# OPTIONS --with-K #-}

module Enumeration.Approach1Simple where

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
\end{code}

%<*pure>
\begin{code}
pure : A → Hierarchy A
pure x zero    = [ x ]
pure x (suc n) = []
\end{code}
%</pure>

%<*rec>
\begin{code}
{-
rec : Builder A A
rec B zero    = []
rec B (suc n) = B n
-}
\end{code}
%</rec>

\begin{code}

interleave : List A → List A → List A
interleave [] ys = ys
interleave (x ∷ xs) ys = x ∷ interleave ys xs

\end{code}

%<*alternative>
\begin{code}
_⟨∣⟩_ : Hierarchy A → Hierarchy B → Hierarchy (A ⊎ B)
(V₁ ⟨∣⟩ V₂) n = interleave (mapL inl (V₁ n)) (mapL inr (V₂ n))
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
{-
pair : Builder A B → Builder A C → Builder A (B × C)
pair B₁ B₂ V n =
     (downFrom (suc n) >>= λ i → (prod (B₁ V n) (B₂ V i)))
  ++ (downFrom n       >>= λ i → (prod (B₁ V i) (B₂ V n)))
-}
\end{code}
%</pair>

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
{-# TERMINATING #-}
ghierarchy : ∀ D {E} → Hierarchy (⟦ D ⟧ (μ E))
ghierarchy one     = pure tt
ghierarchy var zero    = []
ghierarchy var (suc n) = mapL con (ghierarchy _ n)
ghierarchy (D ⊗ E) n = 
     (downFrom (suc n) >>= λ i → (prod (ghierarchy D n) (ghierarchy E i))) -- i ≤ n I promise :)
  ++ (downFrom n       >>= λ i → (prod (ghierarchy D i) (ghierarchy E n))) -- you can check that this is ok by removing the pragma and replace i with n
ghierarchy (D ⊕ E) n = interleave (mapL inl (ghierarchy D n)) (mapL inr (ghierarchy E n))
\end{code}

\begin{code}
hierarchy : ∀ D → Hierarchy (μ D)
hierarchy D = mapH con (ghierarchy D)
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
