
open import Function

open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament

module Orn.Reornament.Algebra 
           {I K : Set }
           {D : func  K K}
           {u : I → K}
           (o : orn D u u) where

open import Orn.Reornament
open import Orn.Ornament.Algebra {u = forgetIdx} (⌈ o ⌉)

reornAlgebra : ⟦ ⌈ o ⌉D ⟧func (μ ⟦ o ⟧orn ∘ forgetIdx) ⇒ μ ⟦ o ⟧orn ∘ forgetIdx
reornAlgebra {i} = forgetAlg {i} 

forgetReornament : μ ⌈ o ⌉D ⇒ μ ⟦ o ⟧orn ∘ forgetIdx
forgetReornament {i} xs = fold ⌈ o ⌉D (λ {i} → reornAlgebra {i}) {i} xs