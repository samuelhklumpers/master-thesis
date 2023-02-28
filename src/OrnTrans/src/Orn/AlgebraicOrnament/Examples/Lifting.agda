

module Orn.AlgebraicOrnament.Examples.Lifting 
           {K : Set }
           {X : K → Set }
       where

open import Function

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Examples.Nat

open import Orn.Ornament
import Orn.AlgebraicOrnament


[_]^ : (D : func  K K) → orn D proj₁ proj₁
[ D ]^ = algOrn
  where open Orn.AlgebraicOrnament.Func {K}{μ D} D ⟨_⟩