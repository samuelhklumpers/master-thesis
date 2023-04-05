open import Function

open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Induction

module IDesc.Case
          {I : Set}
          (D : func  I I)
          (P : {i : I} → μ D i → Set)
       where

Cases : Set 
Cases = {i : I}(xs : ⟦ D ⟧func (μ D) i) → P ⟨ xs ⟩ 

case : Cases → {i : I}(x : μ D i) → P x
case cs = induction D P (λ {i} {xs} _ → cs {i} xs)