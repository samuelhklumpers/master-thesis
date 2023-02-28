module FunOrn.FunOrnament.Examples.Lookup where

open import Data.Unit

open import Logic.Logic

open import IDesc.Examples.Nat

open import Orn.Ornament
open import Orn.Ornament.Identity
open import Orn.Ornament.Examples.List
open import Orn.Ornament.Examples.Maybe

open import FunOrn.Functions.Examples.Le

open import FunOrn.FunOrnament

-- Paper: Example 5.8
typeLookup : (A : Set) → FunctionOrn type<
typeLookup A = μ⁺ idO NatD [ inv tt ]→ 
               μ⁺ ListO A [ inv tt ]→ 
               μ⁺ MaybeO A [ inv tt ]× `⊤