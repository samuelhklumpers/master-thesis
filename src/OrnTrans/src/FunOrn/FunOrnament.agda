module FunOrn.FunOrnament where

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic
open import Logic.IProp

open import IDesc.IDesc
open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Ornament.Algebra 

open import FunOrn.Functions

-- Paper: Definition 5.5
data FunctionOrn : Type  → Set₁ where
  μ⁺_[_]→_ : ∀{I I⁺ : Set}{D : func  I I}{i}{T : Type}
              {u : I⁺ → I} → 
                 (o : orn D u u)(i⁻¹ : u ⁻¹ i)
                 (T⁺ : FunctionOrn T) → FunctionOrn (μ D [ i ]→ T)
  μ⁺_[_]×_ : ∀{I I⁺ : Set}{D : func  I I}{i}{T : Type}
              {u : I⁺ → I} →
                 (o : orn D u u)(i⁻¹ : u ⁻¹ i)
                 (T⁺ : FunctionOrn T) → FunctionOrn (μ D [ i ]× T)
  `⊤ : FunctionOrn `⊤

-- * Projections

-- ** Lifted function

-- Paper: Definition 5.6
⟦_⟧FunctionOrn : ∀{T} → FunctionOrn T → Set 
⟦ μ⁺ o [ inv i⁺ ]→ T⁺ ⟧FunctionOrn = μ ⟦ o ⟧orn i⁺ → ⟦ T⁺ ⟧FunctionOrn
⟦ μ⁺ o [ inv i⁺ ]× T⁺ ⟧FunctionOrn = μ ⟦ o ⟧orn i⁺ × ⟦ T⁺ ⟧FunctionOrn
⟦ `⊤ ⟧FunctionOrn = ⊤

-- ** Coherence proof

-- Paper: Definition 5.7
⟦_⟧Coherence : ∀{T} → (fo : FunctionOrn T) → ⟦ T ⟧Type → ⟦ fo ⟧FunctionOrn → Set 
⟦ μ⁺ o [ inv i⁺ ]→ T⁺ ⟧Coherence f f⁺ = 
  (x⁺ : μ ⟦ o ⟧orn i⁺) → ⟦ T⁺ ⟧Coherence (f (forget o x⁺)) (f⁺ x⁺)
⟦ μ⁺ o [ inv i⁺ ]× T⁺ ⟧Coherence (x , xs) (x⁺ , xs⁺) = 
  (⊢ x ≡ forget o x⁺) × ⟦ T⁺ ⟧Coherence xs xs⁺ 
⟦ `⊤ ⟧Coherence tt tt = ⊤
  