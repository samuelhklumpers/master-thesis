module IDesc.Examples.Bool where

open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (lift)

open import IDesc.IDesc
open import IDesc.Fixpoint


-- Paper: Example 3.6

BoolD : func ⊤ ⊤
BoolD = func.mk λ _ → 
        `σ 2 (λ { zero → `1 
                ; (suc zero) → `1 
                ; (suc (suc ())) })

Bool : Set 
Bool = μ BoolD tt

true : Bool
true = ⟨ zero , tt ⟩

false : Bool
false = ⟨ suc zero , tt ⟩