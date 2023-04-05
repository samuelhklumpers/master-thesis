 

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Fold 
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.InitialAlgebra

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 6.4
-- Typeset: lift_{Alg}
liftAlg : ∀{T} → Alg D (λ _ → ⟦ T ⟧Type) → FunctionOrn T → Set 
liftAlg α T⁺ = Alg ⌈ o ⌉D (λ ix → Patch (fold D α (proj₂ ix)) T⁺)

-- Paper: Definition 6.5
lift-fold : {i : I}{i⁺ : u ⁻¹ i}
          {T : Type }{T⁺ : FunctionOrn T}
          (α : Alg D (λ _ → ⟦ T ⟧Type))
          (β : liftAlg α T⁺) →
    Patch (fold D α) (μ⁺ o [ i⁺ ]→ T⁺)
lift-fold {i⁺ = inv i⁺} α β = 
  λ x x⁺⁺ → fold ⌈ o ⌉D (λ {ix} ih → β {ix} ih) x⁺⁺
