module FunOrn.Functions where

open import Data.Unit
open import Data.Product

open import IDesc.IDesc
open import IDesc.Fixpoint

infixr 20 μ_[_]→_
infixr 20 μ_[_]×_

-- Paper: Definition 5.1

data Type : Set₁ where
  μ_[_]→_ : {I : Set}(D : func  I I)(i : I)(T : Type) → Type 
  μ_[_]×_ : {I : Set}(D : func  I I)(i : I)(T : Type) → Type 
  `⊤ : Type 

⟦_⟧Type : Type → Set 
⟦ μ D [ i ]→ T ⟧Type = μ D i → ⟦ T ⟧Type
⟦ μ D [ i ]× T ⟧Type = μ D i × ⟦ T ⟧Type
⟦ `⊤ ⟧Type = ⊤

