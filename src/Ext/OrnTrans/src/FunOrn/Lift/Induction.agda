

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Induction
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.Induction

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 6.6
liftIH : {T : Type } → DAlg D (λ _ → ⟦ T ⟧Type) → FunctionOrn T → Set 
liftIH α T⁺ = DAlg ⌈ o ⌉D ((λ {ix} _ → Patch (induction D _ α (proj₂ ix)) T⁺))

-- Paper: Definition 6.7
lift-ind : {i : I}{i⁺ : u ⁻¹ i}
          {T : Type }{T⁺ : FunctionOrn T}
          (α : DAlg D (λ _ → ⟦ T ⟧Type))
          (β : liftIH α T⁺) →
    Patch (induction D (λ _ → ⟦ T ⟧Type) α)
          (μ⁺ o [ i⁺ ]→ T⁺)
lift-ind {i⁺ = inv i⁺} α β = 
  λ x x⁺⁺ → induction ⌈ o ⌉D _ (λ {ix} → β {ix}) x⁺⁺
