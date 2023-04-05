module Orn.Algebra.VerticalComposition 
          {I J K L M N : Set}
          {u₁ : K → I}
          {v₁ : L → J}
          {u₂ : M → K}
          {v₂ : N → L} where

open import Function

open import Logic.Logic

open import IDesc

open import Orn.Ornament


compose : {D : func I J} → 
          (o₁ : orn D u₁ v₁) →
          orn ⟦ o₁ ⟧orn u₂ v₂ →
          orn D (u₁ ∘ u₂) (v₁ ∘ v₂)
compose o₁ o₂ = 
         orn.mk (λ j → help (orn.out o₁ (v₂ j)))
  where ins : ∀{i} → Orn u₂ ⟦ {!!} ⟧Orn  → Orn (u₁ ∘ u₂) (`var (u₁ i))
        ins o = {!!}

        help : {D : IDesc_} → (O₁ : Orn u₁ D) → Orn u₂ ⟦ O₁ ⟧Orn → Orn (u₁ ∘ u₂) D 
        help (insert S D⁺) O₂ = insert S (λ s → help (D⁺ s) O₂)
        help (`var (inv i)) O₂ = {!!}
        help `1 O₂ = `1
        help (o₁ `× o₂) O₂ = help o₁ O₂ `× help o₂ O₂
        help (`σ T⁺) O₂ = `σ λ s → help (T⁺ s) O₂
        help (`Σ T⁺) O₂ = `Σ λ s → help (T⁺ s) O₂
        help (`Π T⁺) O₂ = `Π λ s → help (T⁺ s) O₂
        help (deleteΣ s o) O₂ = deleteΣ s (help o O₂)
        help (deleteσ k o) O₂ = deleteσ k (help o O₂)