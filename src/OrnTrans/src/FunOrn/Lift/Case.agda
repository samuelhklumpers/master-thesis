

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Case
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.Fixpoint
open import IDesc.Case

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

liftCases : ∀{T} → Cases D (λ _ → ⟦ T ⟧Type) → FunctionOrn T → Set 
liftCases α T⁺ = Cases ⌈ o ⌉D 
                       (λ {ix} xs → Patch (case D _ α (proj₂ ix)) T⁺)

-- Paper: Definition 6.8
lift-case : {i : I}{i⁺ : u ⁻¹ i}
           {T : Type }{T⁺ : FunctionOrn T}
           (α : Cases D (λ _ → ⟦ T ⟧Type))
           (β : liftCases α T⁺)  →
    Patch (case D (λ _ → ⟦ T ⟧Type) α) (μ⁺ o [ i⁺ ]→ T⁺)
lift-case {i⁺ = inv i⁺} α β = 
  λ x x⁺⁺ → case ⌈ o ⌉D _  (λ {i} xs → β {i} xs) x⁺⁺
