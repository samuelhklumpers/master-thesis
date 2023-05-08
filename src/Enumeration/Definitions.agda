module Enumeration.Definitions where

open import Prelude hiding (rec)
open import Data.List renaming (map to mapL)
open import Data.List.Instances
open import Effect.Monad
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open RawMonad {ℓ-zero} listMonad using (_>>=_)

-- an enumeration as a way to list all elements of a type
module Wrong1 where
  Enum : Type → Type
  Enum A = List A
  -- nice try but infinite types exists, infinite lists do not

module Different1 where
  Enum : Type → Type → Type
  Enum A B = List A → List B
  -- probably right, also completely unique account of enumeration

Hierarchy : Type → Type
Hierarchy A = ℕ → List A

mapH : (A → B) → Hierarchy A → Hierarchy B
mapH f V n = mapL f (V n)

data In {A : Type} (a : A) : List A → Type where
  here  : ∀ {as}             → In a (a ∷ as)
  there : ∀ {b as} → In a as → In a (b ∷ as)

Complete : Hierarchy A → Type
Complete V = ∀ a → Σ[ n ∈ ℕ ] In a (V n)

Unique : Hierarchy A → Type
Unique V = ∀ a n m (i : In a (V n)) (j : In a (V m)) → Σ[ p ∈ n ≡ m ] PathP (λ i → In a (V (p i))) i j 

Builder : (A B : Type) → Type
Builder A B = Hierarchy A → Hierarchy B

-- straight out of A Completely Unique Account of Enumeration
pure : B → Builder A B
pure x _ zero    = [ x ]
pure x _ (suc n) = []

rec : Builder A A
rec B zero    = []
rec B (suc n) = B n

interleave : List A → List A → List A
interleave [] ys = ys
interleave (x ∷ xs) ys = x ∷ interleave ys xs

_⟨∣⟩_ : Builder A B → Builder A C → Builder A (B ⊎ C)
(B₁ ⟨∣⟩ B₂) V n = interleave (mapL inl (B₁ V n)) (mapL inr (B₂ V n))

prod : List A → List B → List (A × B)
prod []       ys       = []
prod (x ∷ xs) []       = []
prod (x ∷ xs) (y ∷ ys) = (x , y) ∷ interleave (mapL (x ,_) ys) (prod xs (y ∷ ys))

pair : Builder A B → Builder A C → Builder A (B × C)
pair B₁ B₂ V n =
     (downFrom (suc n) >>= λ i → (prod (B₁ V n) (B₂ V i)))
  ++ (downFrom n       >>= λ i → (prod (B₁ V i) (B₂ V n)))

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

builder : ∀ {D} D' → Builder (μ D) (⟦ D' ⟧ (μ D))
builder one     = pure tt
builder var     = rec
builder (D ⊗ E) = pair (builder D) (builder E)
builder (D ⊕ E) = builder D ⟨∣⟩ builder E

TreeD : Desc
TreeD = one ⊕ (var ⊗ var)

Tree = μ TreeD

gbuilder : ∀ D → Builder (μ D) (μ D)
gbuilder D V = mapH con (builder D V)

iterate : ℕ → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = f (iterate n f x)

build : Builder A A → Hierarchy A
build B n = iterate (suc n) B (const []) n

hierarchy : ∀ D → Hierarchy (μ D)
hierarchy D = build (gbuilder D)

TreeH = hierarchy TreeD

-- seems good
-- we chop off 0 compared to unique account
