module FunOrn.Patch where



open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament

-- Paper: Definition 5.15
Patch : ∀{T : Type } → ⟦ T ⟧Type → FunctionOrn T → Set 
Patch {T = μ D [ ._ ]→ T} f (μ⁺ o [ inv i⁺ ]→ T⁺) = 
      (x : μ D _) → 
         μ ⌈ o ⌉D (i⁺ , x) → Patch (f x) T⁺
Patch {T = μ D [ ._ ]× T} (x , t) (μ⁺ o [ inv i⁺ ]× T⁺) =
      μ ⌈ o ⌉D (i⁺ , x) × Patch t T⁺
Patch {T = `⊤} tt `⊤ = ⊤
