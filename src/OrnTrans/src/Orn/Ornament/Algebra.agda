
open import Function

open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (fold)

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament

module Orn.Ornament.Algebra 
           {I K : Set}
           {D : func  K K}
           {u : I → K}
           (o : orn D u u) where

open import Orn.Ornament.CartesianMorphism o

-- Paper: Definition 4.14
forgetAlg : Alg ⟦ o ⟧orn (μ D ∘ u)
forgetAlg xs = ⟨ forgetNT xs ⟩ 

-- Paper: Definition 4.15
forget : {i : I} → μ ⟦ o ⟧orn i → μ D (u i)
forget = fold ⟦ o ⟧orn forgetAlg
