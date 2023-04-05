module FunOrn.FunOrnament.Examples.Append where

open import Data.Unit

open import Logic.Logic

open import IDesc.Examples.Nat

open import Orn.Ornament
open import Orn.Ornament.Examples.List

open import FunOrn.Functions.Examples.Plus

open import FunOrn.FunOrnament

-- Paper: Example 5.10
typeAppend : (A : Set) → FunctionOrn type+
typeAppend A = μ⁺ ListO A [ inv tt ]→ 
               μ⁺ ListO A [ inv tt ]→ 
               μ⁺ ListO A [ inv tt ]× `⊤