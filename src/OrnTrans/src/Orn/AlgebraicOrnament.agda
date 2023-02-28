

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Induction

open import Orn.Ornament.Examples.Lifting
open import Orn.Ornament


module Orn.AlgebraicOrnament
           {K : Set }
           {X : K → Set } where

I : Set 
I = Σ K X

u : I → K
u = proj₁

module Desc
         (k : K)
         (x : X k)
         (D : IDesc  K)
         (α : ⟦ D ⟧ X → X k) where

  algOrn :  Orn u D
  algOrn = insert (⟦ D ⟧ X) λ xs →
           insert (α xs ≡ x) λ _ → 
           □h {L = K} D xs

  algOrnD : IDesc  I
  algOrnD = ⟦ algOrn ⟧Orn

module Func 
         (D : func  K K)
         (α : Alg D X) where

  algOrn : orn D u u
  algOrn = orn.mk λ { (k , xs) → Desc.algOrn k xs (func.out D k) (α {k}) }

  -- Paper: Section 4.4
  -- Typeset: algOrnD D α = D^α
  algOrnD : func  I I
  algOrnD = ⟦ algOrn ⟧orn

open Func public

