module Trees.NestedOrnaments where

--open import Prelude.UseAs
--open import Prelude hiding (⟨_⟩)

open import Data.Product
open import Data.List
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String
open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)

private variable
  a b c : Level
  X Y Z : Set a
  x y z : X


data Poly a : Set (ℓ-suc a)
data U a : Set (ℓ-suc a) where
  set : (X : Set a)            → U a
  app : (p : Poly a) (u : U a) → U a
  par :                          U a
  
data Poly a where
  Id  : Poly a
  K   : (u : U a)      → Poly a
  _+_ : (l r : Poly a) → Poly a
  _*_ : (l r : Poly a) → Poly a

⟦_⟧ₚ : Poly a → Set a → Set a
⟦_⟧ᵤ : U a → Set a → Set a
⟦ set X   ⟧ᵤ A = X
⟦ app p u ⟧ᵤ A = ⟦ p ⟧ₚ (⟦ u ⟧ᵤ A)
⟦ par     ⟧ᵤ A = A

⟦ Id ⟧ₚ A = A
⟦ K u ⟧ₚ A = ⟦ u ⟧ᵤ A
⟦ p + q ⟧ₚ A = ⟦ p ⟧ₚ A ⊎ ⟦ q ⟧ₚ A
⟦ p * q ⟧ₚ A = ⟦ p ⟧ₚ A × ⟦ q ⟧ₚ A

-- rather than doing full contexts, let's stick to a single parameter
data RDesc (I : Set a) b : Set (ℓ-suc (ℓ-max a b)) where
  ṿ : (is : List (U b × I)) → RDesc I b 
  σ : (u : U b) (D : ∀ X → ⟦ u ⟧ᵤ X → RDesc I b) → RDesc I b

Desc : Set a → (b : Level) → Set (ℓ-suc (ℓ-max a b))
Desc I b = I → RDesc I b

-- unfortunately naturals now have a parameter
NatD : Desc ⊤ ℓ-zero
NatD _ = σ (set Bool) λ X → λ
  { false → ṿ []
  ; true  → ṿ [ (par , _) ] }

ListD : Desc ⊤ ℓ-zero
ListD _ = σ (set Bool) λ X → λ
  { false → ṿ []
  ; true  → σ par λ _ _ → ṿ [ (par , _) ] }

PTreeD : Desc ⊤ ℓ-zero
PTreeD _ = σ (set Bool) λ X → λ
  { false → σ par λ _ _ → ṿ []
  ; true  → ṿ [ (app (Id * Id) par , _) ] }


DFun : {X : Set a} → Desc X b → (Set b → X → Set (ℓ-suc (ℓ-max a b))) → Set b → X → Set (ℓ-suc (ℓ-max a b))
--{-# NO_POSITIVITY_CHECK #-}
data μ {X : Set a} (D : Desc X b) (Y : Set b) : X → Set (ℓ-suc (ℓ-max a b)) where
  con : ∀ {i} → DFun D (μ D) Y i → μ D Y i

Prod : {X : Set a} → List (U b × X) → (Set b → X → Set (ℓ-suc (ℓ-max a b))) → Set b → Set (ℓ-suc (ℓ-max a b))
Prod []             f Y = Lift _ ⊤
Prod ((u , i) ∷ xs) f Y = f (⟦ u ⟧ᵤ Y) i × Prod xs f Y

RDFun : {X : Set a} → RDesc X b → (Set b → X → Set (ℓ-suc (ℓ-max a b))) → Set b → Set (ℓ-suc (ℓ-max a b)) 
RDFun (ṿ is)  f Y = Prod is f Y
RDFun (σ u D) f Y = Σ[ s ∈ ⟦ u ⟧ᵤ Y ] RDFun (D Y s) f Y 

DFun D f Y i = RDFun (D i) f Y

List′ = μ ListD

List-ex : List′ String tt
List-ex = con (true , ("a" , con (false , _) , _))

PTree = μ PTreeD

PTree-ex : PTree String tt
PTree-ex = con (true , (con (true , con (false , (("a" , "b") , ("c" , "d")) , _) , _) , _))


-- and now
-- 1. adapt heterogenization
-- 2. give NDesc → Desc
