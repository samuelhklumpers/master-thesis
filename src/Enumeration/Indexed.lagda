\begin{code}
{-# OPTIONS --with-K --guardedness #-}

module Enumeration.Indexed where

open import Prelude hiding (rec)
open import Data.List renaming (map to mapL)
open import Data.List.Instances
open import Codata.Musical.Colist
open import Effect.Monad
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open RawMonad {ℓ-zero} listMonad using (_>>=_)


private variable
  Ix : Type
\end{code}

%<*hierarchy>
\begin{code}
Hierarchy : (Ix : Type) → (Ix → Type) → Type
Hierarchy Ix F = ℕ → (Colist Ix × ((i : Ix) → ℕ × List (F i)))
\end{code}
%</hierarchy>


%<*Desc>
\begin{code}
data Desc (I : Set) : Set where
  one : Desc I
  var : I → Desc I
  _⊗_ : (D E : Desc I) → Desc I
  _⊕_ : (D E : Desc I) → Desc I

IDesc : (Ix : Type) → Type
IDesc Ix = Ix → Desc Ix

⟦_⟧ : Desc Ix → (Ix → Set) → Set
⟦ one ⟧   X = ⊤
⟦ var i ⟧ X = X i
⟦ D ⊗ E ⟧ X = ⟦ D ⟧ X × ⟦ E ⟧ X
⟦ D ⊕ E ⟧ X = ⟦ D ⟧ X ⊎ ⟦ E ⟧ X

data μ (D : IDesc Ix) (i : Ix) : Set where
  con : ⟦ D i ⟧ (μ D) → μ D i
\end{code}
%</Desc>

<%*Counter>
\begin{code}
data Counter : ℕ → Set where
  yes : Counter 2
  no  : ∀ {n} → Counter (2 · n) → Counter (3 · n)

counter-3 : Counter 3
counter-3 = no {n = 1} yes
\end{code}
<%/Counter>


-- \begin{code}
-- mapH : (A → B) → Hierarchy A → Hierarchy B
-- mapH f V n with V n
-- ... | c , xs = c , mapL f xs
-- \end{code}

-- %<*pure>
-- \begin{code}
-- pure : A → Hierarchy A
-- pure x zero    = 1 , [ x ]
-- pure x (suc n) = 0 , []
-- \end{code}
-- %</pure>

-- \begin{code}
-- interleave : List A → List A → List A
-- interleave [] ys = ys
-- interleave (x ∷ xs) ys = x ∷ interleave ys xs
-- \end{code}

-- %<*alternative>
-- \begin{code}
-- _⟨∣⟩_ : Hierarchy A → Hierarchy B → Hierarchy (A ⊎ B)
-- (V₁ ⟨∣⟩ V₂) n with V₁ n | V₂ n
-- ... | c₁ , xs | c₂ , ys = c₁ + c₂ , interleave (mapL inl xs) (mapL inr ys)
-- \end{code}
-- %</alternative>

-- \begin{code}
-- prod : List A → List B → List (A × B)
-- prod []       ys       = []
-- prod (x ∷ xs) []       = []
-- prod (x ∷ xs) (y ∷ ys) = (x , y) ∷ interleave (mapL (x ,_) ys) (prod xs (y ∷ ys))
-- \end{code}

-- \begin{code}
-- _++′_ : (l r : ℕ × List A) → ℕ × List A
-- (n , xs) ++′ (m , ys) = n + m , xs ++ ys

-- prod′ : ℕ × List A → ℕ × List B → ℕ × List (A × B)
-- prod′ (n , xs) (m , ys) = n · m , prod xs ys

-- ⊛-left : Hierarchy A → Hierarchy B → ℕ → Hierarchy (A × B)
-- ⊛-left V₁ V₂ n zero    = prod′ (V₁ n) (V₂ 0)
-- ⊛-left V₁ V₂ n (suc m) = prod′ (V₁ n) (V₂ (suc m)) ++′ ⊛-left V₁ V₂ n m

-- ⊛-right : Hierarchy A → Hierarchy B → ℕ → Hierarchy (A × B)
-- ⊛-right V₁ V₂ n zero    = 0 , []
-- ⊛-right V₁ V₂ n (suc m) = prod′ (V₁ m) (V₂ n) ++′ ⊛-right V₁ V₂ n m

-- _⊛_ : Hierarchy A → Hierarchy B → Hierarchy (A × B)
-- (V₁ ⊛ V₂) n = ⊛-left V₁ V₂ n n ++′ ⊛-right V₁ V₂ n n
-- \end{code}

-- -- %<*ghierarchy>
-- -- \begin{code}
-- -- {-# TERMINATING #-}
-- -- ghierarchy : ∀ D {E} → Hierarchy (⟦ D ⟧ (μ E))
-- -- ghierarchy one     = pure tt
-- -- ghierarchy var zero    = 0 , []
-- -- ghierarchy var (suc n) = mapH con (ghierarchy _) n
-- -- ghierarchy (D ⊗ E) = ghierarchy D  ⊛  ghierarchy E
-- -- ghierarchy (D ⊕ E) = ghierarchy D ⟨∣⟩ ghierarchy E
-- -- -- note that the termination checker also does not like this case,
-- -- -- so inline it if you want to get rid of the pragma
-- -- \end{code}
-- -- %</ghierarchy>

-- -- \begin{code}
-- -- hierarchy : ∀ D → Hierarchy (μ D)
-- -- hierarchy D = mapH con (ghierarchy D)
-- -- \end{code}

-- -- %<*TreeD>
-- -- \begin{code}
-- -- TreeD : Desc
-- -- TreeD = one ⊕ (var ⊗ var)

-- -- TreeH = hierarchy TreeD
-- -- \end{code}
-- -- %</TreeD>

-- -- \begin{code}
-- -- Tree′ = μ TreeD

-- -- data Tree : Type where
-- --   leaf : Tree
-- --   node : Tree → Tree → Tree

-- -- conversion : Tree′ → Tree
-- -- conversion (con (inl _))       = leaf
-- -- conversion (con (inr (l , r))) = node (conversion l) (conversion r)
-- -- \end{code}

-- -- %<*numTrees>
-- -- \begin{code}
-- -- numTrees : ℕ → ℕ
-- -- numTrees n = fst (TreeH n)
-- -- \end{code}
-- -- %</numTrees>

-- -- \begin{code}
-- -- trees : ℕ → List Tree
-- -- trees n = mapL conversion (snd (TreeH n))

-- -- trees-2 : List Tree
-- -- trees-2 =
-- -- \end{code}
-- -- %<*trees-2>
-- -- \begin{code}
-- --     node (node leaf leaf) (node leaf leaf)
-- --   ∷ node (node leaf leaf) leaf
-- --   ∷ node leaf             (node leaf leaf)
-- --   ∷ []
-- -- \end{code}
-- -- %</trees-2>
