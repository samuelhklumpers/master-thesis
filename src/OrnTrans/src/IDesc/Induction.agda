
open import Function

open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Lifting


module IDesc.Induction
          {I : Set}
          (D : func  I I)
          (P : {i : I} → μ D i → Set)
       where

DAlg : Set
DAlg = {i : I}{xs : ⟦ D ⟧func (μ D) i} → 
       □ D P (i , xs) → P ⟨ xs ⟩

module Induction (α : DAlg) where

  mutual
    induction : {i : I}(x : μ D i) → P x
    induction ⟨ xs ⟩ = α (hyps (func.out D _) xs)
  
    hyps : (D' : IDesc  I)(xs : ⟦ D' ⟧ (μ D)) → □h D' P xs
    hyps `1 tt = tt
    hyps (`var i) xs = induction xs
    hyps (T `× T') (t , t') = hyps T t , hyps T' t'
    hyps (`σ n T) (k , xs) = hyps (T k) xs
    hyps (`Σ S T) (s , xs) = hyps (T s) xs
    hyps (`Π S T) f = λ s → hyps (T s) (f s)

induction : DAlg → {i : I}(x : μ D i) → P x
induction = Induction.induction