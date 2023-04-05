

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Constructor
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.Fixpoint
open import IDesc.Induction

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch
open import FunOrn.Lift.MkReorn o

-- Paper: Definition 6.17
lift-constructor : {i : I}{i⁺ : u ⁻¹ i}
                  {T : Type }{T⁺ : FunctionOrn T}
                  {t : ⟦ T ⟧Type} →
                  {x : ⟦ D ⟧func (μ D) i}
                  (e : Extra {i⁺ = i⁺} x) → Args {i⁺ = i⁺} x e → Patch t T⁺ →
                  Patch (⟨ x ⟩ , t) (μ⁺ o [ i⁺ ]× T⁺)
lift-constructor {i⁺ = inv i⁺} e a p = mkreorn e a , p
