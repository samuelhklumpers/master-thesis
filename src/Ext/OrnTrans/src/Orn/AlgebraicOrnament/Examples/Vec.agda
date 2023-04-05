module Orn.AlgebraicOrnament.Examples.Vec 
         (A : Set)
       where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Examples.Nat

open import Orn.Ornament
open import Orn.Ornament.Examples.List

open import Orn.Ornament.Algebra (ListO A)
import Orn.AlgebraicOrnament
open Orn.AlgebraicOrnament.Func (⟦ ListO A ⟧orn) forgetAlg

Vec : Nat → Set
Vec n = μ algOrnD (tt , n)

vnil : Vec ze
vnil = ⟨ (zero , tt) , refl , tt ⟩

vcons : ∀{n} → A → Vec n → Vec (su n)
vcons {n} a xs = ⟨ (suc zero , a , n) , 
                   refl , xs ⟩
