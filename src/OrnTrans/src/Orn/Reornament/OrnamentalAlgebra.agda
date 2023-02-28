open import Function

open import Logic.Logic

open import IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament

module Orn.Reornament.OrnamentalAlgebra 
           {I K : Set}
           {D : func K K}
           (u : I → K)
           (o : orn D u u) where

open import Orn.Reornament u o
open import Orn.Ornament.Algebra forgetIdx reorn

reornAlgebra : ⟦ reornD ⟧func (μ ⟦ o ⟧orn ∘ forgetIdx) ⇒ μ ⟦ o ⟧orn ∘ forgetIdx
reornAlgebra = ornAlgebra

forgetReornament : μ reornD ⇒ (μ ⟦ o ⟧orn ∘ forgetIdx)
forgetReornament = fold reornD reornAlgebra