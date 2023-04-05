module FunOrn.Patch.Apply where



open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Ornament.Algebra 
open import Orn.Reornament
open import Orn.Reornament.Make
open import Orn.Reornament.Algebra

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 5.22
patch : {T : Type } → (fo : FunctionOrn T)(f : ⟦ T ⟧Type) → 
        Patch f fo → ⟦ fo ⟧FunctionOrn
patch (μ⁺ o [ inv i⁺ ]→ T⁺) f p = 
  λ x → patch T⁺ (f (forget o x)) 
                 (p (forget o x)
                    (make o x))
patch (μ⁺ o [ inv i⁺ ]× T⁺) (x , xs) (x⁺⁺ , p) =
  forgetReornament o x⁺⁺ , patch T⁺ xs p
patch `⊤ tt tt = tt
