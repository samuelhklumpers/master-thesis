module FunOrn.Patch.Coherence where



open import Data.Unit
open import Data.Product

open import Logic.Logic
open import Logic.IProp

open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Ornament.Algebra 
open import Orn.Reornament
open import Orn.Reornament.Make
open import Orn.Reornament.Algebra
open import Orn.Reornament.Coherence

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch
open import FunOrn.Patch.Apply

-- Paper: Definition 5.23
⊢Coherence : {T : Type } → (T⁺ : FunctionOrn T)(f : ⟦ T ⟧Type)
             (p : Patch f T⁺) → ⟦ T⁺ ⟧Coherence f (patch T⁺ f p)
⊢Coherence (μ⁺ o [ inv i⁺ ]→ T⁺) f f⁺ = 
  λ x → ⊢Coherence T⁺ 
                   (f (forget o x)) 
                   (f⁺ (forget o x)
                       (make o x))
⊢Coherence (μ⁺ o [ inv i⁺ ]× T⁺) (x , xs) (x⁺ , xs⁺) = 
  coherentOrn o x⁺ , ⊢Coherence T⁺ xs xs⁺
⊢Coherence `⊤ tt tt = tt

