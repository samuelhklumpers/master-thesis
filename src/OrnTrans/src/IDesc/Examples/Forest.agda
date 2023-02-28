module IDesc.Examples.Forest where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product

open import IDesc.IDesc
open import IDesc.Fixpoint

TreeKind : Set
TreeKind = Fin 2

pattern `NTree = zero
pattern `NForest = suc zero

NTreeD : Set → func TreeKind TreeKind
NTreeD A = func.mk (λ { `NTree → `Σ A (λ _ → `var `NForest `× `1 ) 
                      ; `NForest → `Σ (Fin 2) λ 
                                   { zero → `1 
                                   ; (suc zero) → `var `NTree `× `var `NForest `× `1  
                                   ; (suc (suc ())) } 
                      ; (suc (suc ())) })

NTree : Set → Set
NTree A = μ (NTreeD A) `NTree

NForest : Set → Set
NForest A = μ (NTreeD A) `NForest

node : ∀{A} → A → NForest A → NTree A 
node a fs = ⟨ a , fs , tt ⟩

nil : ∀{A} → NForest A
nil = ⟨ zero , tt ⟩

cons : ∀{A} → NTree A → NForest A → NForest A
cons t fs = ⟨ suc zero , t , fs , tt ⟩